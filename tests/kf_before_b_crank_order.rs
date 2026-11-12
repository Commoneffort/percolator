//! Crank order must not change who pays a default (#172 follow-up, reported on #212).
//!
//! A loser goes bankrupt; its residual books into B. If the keeper liquidates the loser before
//! the winner is settled, the standalone SettleB crank step used to put the winner's B share on
//! its pnl BEFORE its pending K/F gain arrived. The gain then looked like a cure for a debt and
//! drew backing (or burned face) for a share nobody is owed. spec.md: per leg,
//! net_pnl_delta = KF_pnl_delta - B_loss; requirement 27: residual attribution independent of
//! caller ordering.
//!
//! Each scenario is built twice and settled in both orders; every observable value must agree.
//! A seeded sweep covers many margin / cap / size / backing combinations beyond the three cases
//! reported upstream.

use percolator::{
    AutoCrankObservationV16, AutoCrankPlanV16, AutoCrankWorkV16, EngineAssetSlotV16Account,
    Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PortfolioAccountV16Account,
    PortfolioV16ViewMut, ProvenanceHeaderV16, ProvenanceHeaderV16Account, TradeRequestV16,
    V16Config, BOUND_SCALE, POS_SCALE,
};

const P0: u64 = 10_000;

#[derive(Clone, Copy, Debug)]
struct Scenario {
    im_bps: u64,
    mm_bps: u64,
    cap_bps: u64,
    loser_dep: u128,
    winner_dep: u128,
    units: i128,
    winner_long: bool,
    moves: u32,
    backing: Option<(usize, u128)>,
}

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    winner_equity: i128,
    loser_equity: i128,
    stranded: u128,
    insurance: u128,
    provider_earnings: u128,
    fresh_backing_total: u128,
    // per domain: claims, fresh reserved, spent, provider receivable, bucket unliened
    domains: [[u128; 5]; 2],
}

fn portfolio(seed: u8) -> PortfolioAccountV16Account {
    let h = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new([1; 32], [seed; 32], [3; 32]));
    let mut a = PortfolioAccountV16Account::default();
    a.init_empty_in_place(h).unwrap();
    a
}

fn settle(market: &mut MarketGroupV16ViewMut<'_, u64>, acct: &mut PortfolioV16ViewMut<'_>, slot: u64, price: u64) {
    let obs = [AutoCrankObservationV16 { asset_index: 0, effective_price: price, funding_rate_e9: 0 }];
    for _ in 0..64 {
        let r = market
            .permissionless_auto_crank_not_atomic(
                acct,
                AutoCrankWorkV16 { now_slot: slot, observations: &obs, resolved_close_fee_rate_per_slot: 0 },
            )
            .expect("auto-crank");
        if r.selected == AutoCrankPlanV16::NoAction {
            return;
        }
    }
    panic!("auto-crank did not converge");
}

/// None if the scenario cannot be set up (e.g. the opening trade fails margin).
fn play(s: Scenario, winner_first: bool) -> Option<Snapshot> {
    let mut cfg = V16Config::public_user_fund_with_market_slots(1, 1, 0, 10);
    cfg.initial_margin_bps = s.im_bps;
    cfg.maintenance_margin_bps = s.mm_bps;
    cfg.max_price_move_bps_per_slot = s.cap_bps;
    let mut header = MarketGroupV16HeaderAccount::new_dynamic([1; 32], cfg, 1, 0).ok()?;
    let mut markets = vec![Market::new(0, EngineAssetSlotV16Account::default())];
    header.activate_empty_asset_slot_not_atomic(0, &mut markets[0].engine, P0, 1).ok()?;
    let (mut wa, mut la) = (portfolio(1), portfolio(2));
    let mut market = MarketGroupV16ViewMut::new(&mut header, &mut markets);
    let mut winner = PortfolioV16ViewMut::new(&mut wa);
    let mut loser = PortfolioV16ViewMut::new(&mut la);
    if let Some((d, amt)) = s.backing {
        market.deposit_fresh_counterparty_backing_not_atomic(d, amt, 1_000_000).ok()?;
    }
    market.deposit_not_atomic(&mut winner, s.winner_dep).ok()?;
    market.deposit_not_atomic(&mut loser, s.loser_dep).ok()?;
    let q = s.units * POS_SCALE as i128;
    market
        .execute_trade_with_fee_loss_stale_scoped_not_atomic(
            &mut winner,
            &mut loser,
            TradeRequestV16 { asset_index: 0, size_q: if s.winner_long { q } else { -q }, exec_price: P0, fee_bps: 0 },
        )
        .ok()?;
    let (mut price, mut slot) = (P0, 1u64);
    for _ in 0..s.moves {
        let step = price * s.cap_bps / 10_000;
        price = if s.winner_long { price + step } else { price - step };
        slot += 1;
        market.set_asset_raw_oracle_target_not_atomic(0, price).unwrap();
        market.accrue_asset_to_not_atomic(0, slot, price, 0, true).unwrap();
    }
    if winner_first {
        settle(&mut market, &mut winner, slot, price);
        settle(&mut market, &mut loser, slot, price);
    } else {
        settle(&mut market, &mut loser, slot, price);
        settle(&mut market, &mut winner, slot, price);
    }
    for _ in 0..2 {
        settle(&mut market, &mut winner, slot, price);
        settle(&mut market, &mut loser, slot, price);
    }
    let h = &market.header;
    let owned = h.c_tot.get() + h.insurance.get() + h.backing_provider_earnings_total.get()
        + h.source_fresh_backing_total_num.get() / BOUND_SCALE;
    let e = &market.markets[0].engine;
    let dom = |c: percolator::SourceCreditStateV16, b: percolator::BackingBucketV16| {
        [
            c.positive_claim_bound_num / BOUND_SCALE,
            c.fresh_reserved_backing_num / BOUND_SCALE,
            c.spent_backing_num / BOUND_SCALE,
            c.provider_receivable_num / BOUND_SCALE,
            b.fresh_unliened_backing_num / BOUND_SCALE,
        ]
    };
    Some(Snapshot {
        winner_equity: winner.header.capital.get() as i128 + winner.header.pnl.get(),
        loser_equity: loser.header.capital.get() as i128 + loser.header.pnl.get(),
        stranded: h.vault.get() - owned,
        insurance: h.insurance.get(),
        provider_earnings: h.backing_provider_earnings_total.get(),
        fresh_backing_total: h.source_fresh_backing_total_num.get(),
        domains: [
            dom(e.source_credit_long.try_to_runtime().unwrap(), e.backing_long.try_to_runtime().unwrap()),
            dom(e.source_credit_short.try_to_runtime().unwrap(), e.backing_short.try_to_runtime().unwrap()),
        ],
    })
}

fn both_orders(s: Scenario) -> Option<(Snapshot, Snapshot)> {
    Some((play(s, true)?, play(s, false)?))
}

#[test]
fn winner_is_not_charged_the_default_twice() {
    let s = Scenario { im_bps: 5_000, mm_bps: 2_500, cap_bps: 2_000, loser_dep: 692_730, winner_dep: 904_405, units: 85, winner_long: true, moves: 6, backing: None };
    let (w, l) = both_orders(s).unwrap();
    assert_eq!(w.stranded, 0);
    assert!((w.winner_equity - (904_405 + 692_730)).abs() <= 1, "{w:?}");
    assert_eq!(l, w, "loser-first order changed the outcome");
}

#[test]
fn backing_provider_does_not_pay_the_default() {
    let s = Scenario { im_bps: 2_000, mm_bps: 1_000, cap_bps: 500, loser_dep: 200_000, winner_dep: 1_000_000, units: 100, winner_long: false, moves: 6, backing: Some((0, 78_464)) };
    let (w, l) = both_orders(s).unwrap();
    assert_eq!(w.stranded, 0);
    assert_eq!(l, w, "loser-first order changed the outcome");
}

#[test]
fn small_default_does_not_spend_unowed_backing() {
    let s = Scenario { im_bps: 1_000, mm_bps: 500, cap_bps: 400, loser_dep: 10_000, winner_dep: 100_000, units: 9, winner_long: true, moves: 4, backing: None };
    let (w, l) = both_orders(s).unwrap();
    assert_eq!(l, w, "loser-first order changed the outcome");
}

#[test]
fn solvent_liquidation_control() {
    let s = Scenario { im_bps: 1_000, mm_bps: 500, cap_bps: 400, loser_dep: 10_000, winner_dep: 100_000, units: 9, winner_long: true, moves: 2, backing: None };
    let (w, l) = both_orders(s).unwrap();
    assert_eq!(w.stranded, 0);
    assert_eq!(l, w);
}

/// Seeded sweep: crank order never changes any observable value.
#[test]
fn crank_order_sweep() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut rnd = |n: u64| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x % n
    };
    let n: usize = std::env::var("SWEEP").ok().and_then(|v| v.parse().ok()).unwrap_or(3_000);
    let (mut ran, mut diffs, mut dust) = (0, Vec::new(), 0);
    for _ in 0..n {
        let mm = 200 + rnd(3_000);
        let s = Scenario {
            im_bps: mm * 2,
            mm_bps: mm,
            cap_bps: 100 + rnd(2_500),
            loser_dep: 1_000 + rnd(1_000_000) as u128,
            winner_dep: 1_000 + rnd(2_000_000) as u128,
            units: 1 + rnd(150) as i128,
            winner_long: rnd(2) == 0,
            moves: 1 + rnd(8) as u32,
            backing: if rnd(2) == 0 { None } else { Some((rnd(2) as usize, 1 + rnd(200_000) as u128)) },
        };
        let Some((w, l)) = both_orders(s) else { continue };
        ran += 1;
        if w == l {
            continue;
        }
        // Conservative rounding of a claim face may differ by one atom between orders. Allowed
        // only if nothing is stranded, no backing is spent differently and no value moves to
        // insurance or providers.
        let one_atom = (w.winner_equity - l.winner_equity).abs() <= 1
            && (w.loser_equity - l.loser_equity).abs() <= 1
            && w.stranded == 0
            && l.stranded == 0
            && (w.insurance, w.provider_earnings, w.fresh_backing_total)
                == (l.insurance, l.provider_earnings, l.fresh_backing_total)
            && (0..2).all(|d| {
                (1..5).all(|k| w.domains[d][k] == l.domains[d][k])
                    && w.domains[d][0].abs_diff(l.domains[d][0]) <= 1
            });
        if one_atom {
            dust += 1;
        } else {
            diffs.push(format!("{s:?}\n  winner-first {w:?}\n  loser-first  {l:?}"));
        }
    }
    println!("sweep: {ran} scenarios ran, {} order-dependent, {dust} differ by one rounding atom", diffs.len());
    assert!(ran > n / 3, "too few scenarios set up: {ran}");
    assert!(diffs.is_empty(), "{} order-dependent scenarios, first:\n{}", diffs.len(), diffs[0]);
}
