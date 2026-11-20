//! Randomized whole-life check of a market: trades (gains used as margin -> liens), capped price
//! moves on two assets, liquidations / defaults, fresh backing on random domains with short and
//! long expiries (lapse mid-run), conversions, withdrawals, provider withdrawals, then resolution
//! and a complete wind-down.
//!
//! Checked:
//!  * validate_shape() after every operation (engine's own accounting invariants);
//!  * crank-order independence at checkpoints: the same state is settled in two account orders,
//!    and every account's equity and every domain's backing/claim fields must agree (1 atom of
//!    claim rounding tolerated, nothing stranded);
//!  * conservation at the end: deposits == everything paid out + what is left (insurance) +
//!    what the terminal slab retires. Retired value is value no one received.
//!  * liveness: every account closes and the slab reaches ReadyToClose.
//!
//! Engine-API only, no fees, no funding. RUNS (default 300) and SEED env vars.
//! Prints a summary line; panics only on shape violations (always bugs).

use percolator::{
    AutoCrankObservationV16, AutoCrankPlanV16, AutoCrankWorkV16, EngineAssetSlotV16Account,
    Market, MarketGroupV16HeaderAccount, MarketGroupV16ViewMut, PortfolioAccountV16Account,
    PortfolioV16ViewMut, ProvenanceHeaderV16, ProvenanceHeaderV16Account, ResolvedCloseOutcomeV16,
    TerminalSlabOutcomeV16, TradeRequestV16, V16Config, BOUND_SCALE, POS_SCALE,
};
use std::collections::BTreeMap;

const ASSETS: usize = 2;
const N: usize = 4;
const P0: u64 = 10_000;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

#[derive(Clone, Copy)]
struct World {
    header: MarketGroupV16HeaderAccount,
    markets: [Market<u64>; ASSETS],
    accts: [PortfolioAccountV16Account; N],
    prices: [u64; ASSETS],
    slot: u64,
    trend: [u64; ASSETS],
}

fn portfolio(seed: u8) -> PortfolioAccountV16Account {
    let h = ProvenanceHeaderV16Account::from_runtime(&ProvenanceHeaderV16::new([1; 32], [seed; 32], [3; 32]));
    let mut a = PortfolioAccountV16Account::default();
    a.init_empty_in_place(h).unwrap();
    a
}

#[derive(Default)]
struct Stats {
    runs: u64,
    ops: u64,
    trades_ok: u64,
    liquidations_ok: u64,
    bankrupt_runs: u64,
    lien_runs: u64,
    lapse_runs: u64,
    checkpoints: u64,
    order_diffs: u64,
    order_money: u64,
    deficit_total: i128,
    order_dust: u64,
    crank_errors: BTreeMap<String, u64>,
    resolve_fail: u64,
    stuck_close: u64,
    stuck_slab: u64,
    retired_runs: u64,
    retired_total: u128,
    leftover_runs: u64,
    conservation_breaks: u64,
    examples: Vec<String>,
}

impl World {
    fn with_raw<R>(&mut self, f: impl FnOnce(&mut MarketGroupV16ViewMut<'_, u64>, &mut [PortfolioAccountV16Account; N]) -> R) -> R {
        let mut m = MarketGroupV16ViewMut::new(&mut self.header, &mut self.markets);
        f(&mut m, &mut self.accts)
    }

    /// Like a transaction: if the engine call fails, every change it made is rolled back.
    fn with<T, E>(&mut self, f: impl FnOnce(&mut MarketGroupV16ViewMut<'_, u64>, &mut [PortfolioAccountV16Account; N]) -> Result<T, E>) -> Result<T, E> {
        let saved = (self.header, self.markets, self.accts);
        let r = self.with_raw(f);
        if r.is_err() {
            (self.header, self.markets, self.accts) = saved;
        }
        r
    }

    fn shape(&mut self, what: &str) {
        let r = self.with_raw(|m, accts| {
            m.validate_shape()?;
            for a in accts.iter_mut() {
                let v = PortfolioV16ViewMut::new(a);
                v.validate_with_market(&m.as_view())?;
            }
            Ok::<(), percolator::V16Error>(())
        });
        if let Err(e) = r {
            panic!("shape violated after {what}: {e:?}");
        }
    }

    fn crank(&mut self, i: usize, st: &mut Stats) -> bool {
        let prices = self.prices;
        let slot = self.slot;
        let obs: Vec<AutoCrankObservationV16> = (0..ASSETS)
            .map(|a| AutoCrankObservationV16 { asset_index: a as u16 as _, effective_price: prices[a], funding_rate_e9: 0 })
            .collect();
        let mut ok = true;
        for _ in 0..64 {
            let r = self.with(|m, accts| {
                m.permissionless_auto_crank_not_atomic(
                    &mut PortfolioV16ViewMut::new(&mut accts[i]),
                    AutoCrankWorkV16 { now_slot: slot, observations: &obs, resolved_close_fee_rate_per_slot: 0 },
                )
            });
            match r {
                Ok(r) if r.selected == AutoCrankPlanV16::NoAction => return ok,
                Ok(_) => {}
                Err(percolator::V16Error::NonProgress) => return ok,
                Err(e) => {
                    *st.crank_errors.entry(format!("{e:?}")).or_default() += 1;
                    return false;
                }
            }
        }
        *st.crank_errors.entry("no-fixpoint".into()).or_default() += 1;
        ok = false;
        ok
    }

    fn settle_all(&mut self, order: &[usize], st: &mut Stats) {
        for &i in order {
            self.crank(i, st);
        }
        for _ in 0..2 {
            for i in 0..N {
                self.crank(i, st);
            }
        }
    }

    fn step_price(&mut self, rng: &mut Rng, cap_bps: u64) {
        self.slot += 1;
        for a in 0..ASSETS {
            let r = rng.below(5);
            let max = self.prices[a] * cap_bps / 10_000;
            // Mostly full-cap moves in the asset's trend direction (defaults need big moves).
            let step = if r == 0 { 0 } else if r <= 2 { max } else { 1 + rng.below(max.max(1)) };
            let up = if rng.below(10) < 8 { self.trend[a] == 1 } else { self.trend[a] == 0 };
            self.prices[a] = if up { self.prices[a] + step } else { self.prices[a].saturating_sub(step).max(100) };
        }
        let (prices, slot) = (self.prices, self.slot);
        for a in 0..ASSETS {
            // An asset in recovery / drain may refuse a new target; its accrual still runs.
            let _ = self.with(|m, _| m.set_asset_raw_oracle_target_not_atomic(a as _, prices[a]));
            let _ = self.with(|m, _| m.accrue_asset_to_not_atomic(a as _, slot, prices[a], 0, true));
        }
    }

    fn snapshot(&mut self) -> (Vec<i128>, Vec<[u128; 5]>, u128, u128) {
        let eq = self.accts.iter().map(|a| a.capital.get() as i128 + a.pnl.get()).collect();
        let mut doms = vec![];
        for a in 0..ASSETS {
            let e = &self.markets[a].engine;
            for (c, b) in [(e.source_credit_long, e.backing_long), (e.source_credit_short, e.backing_short)] {
                let c = c.try_to_runtime().unwrap();
                let b = b.try_to_runtime().unwrap();
                doms.push([
                    c.positive_claim_bound_num / BOUND_SCALE,
                    c.fresh_reserved_backing_num / BOUND_SCALE,
                    c.spent_backing_num / BOUND_SCALE,
                    c.provider_receivable_num / BOUND_SCALE,
                    b.fresh_unliened_backing_num / BOUND_SCALE,
                ]);
            }
        }
        let h = &self.header;
        (eq, doms, h.insurance.get(), h.backing_provider_earnings_total.get())
    }
}

fn one_run(seed: u64, st: &mut Stats) {
    let mut rng = Rng(seed | 1);
    let mm = 300 + rng.below(2_500);
    let cap = 50 + rng.below(1_500);
    let mut cfg = V16Config::public_user_fund_with_market_slots(ASSETS as u16, ASSETS as u32, 0, 10);
    cfg.maintenance_margin_bps = mm;
    let cfg_mm = mm;
    cfg.initial_margin_bps = mm * 2;
    cfg.max_price_move_bps_per_slot = cap;
    let mut header = match MarketGroupV16HeaderAccount::new_dynamic([1; 32], cfg, ASSETS as u32, 0) { Ok(h) => h, Err(e) => { *st.crank_errors.entry(format!("setup new_dynamic {e:?}")).or_default() += 1; return } };
    let mut markets = [Market::new(0u64, EngineAssetSlotV16Account::default()), Market::new(1u64, EngineAssetSlotV16Account::default())];
    for a in 0..ASSETS {
        if let Err(e) = header.activate_empty_asset_slot_not_atomic(a as u32, &mut markets[a].engine, P0, 1 + 2 * a as u64) {
            *st.crank_errors.entry(format!("setup activate {a} {e:?}")).or_default() += 1;
            return;
        }
    }
    let (t0, t1) = (rng.below(2), rng.below(2));
    let mut w = World { header, markets, accts: [portfolio(1), portfolio(2), portfolio(3), portfolio(4)], prices: [P0; ASSETS], slot: 1 + 2 * (ASSETS as u64 - 1), trend: [t0, t1] };
    st.runs += 1;
    let mut paid_in: u128 = 0;
    let mut paid_out: u128 = 0;
    let mut max_expiry = 0u64;
    let mut had_lien = false;
    let mut had_lapse = false;
    let mut had_negative = false;
    let mut had_provider = false;

    // Providers.
    let nprov = if std::env::var("LIENS").is_ok() { 2 + rng.below(4) } else { rng.below(4) };
    for _ in 0..nprov {
        let d = rng.below(2 * ASSETS as u64) as usize;
        let amt = 1 + rng.below(300_000) as u128;
        let heavy = std::env::var("LIENS").is_ok();
        let exp = if heavy || rng.below(2) == 0 { 5 + rng.below(40) } else { 1_000_000 };
        max_expiry = max_expiry.max(exp);
        if exp < 1_000_000 {
            had_lapse = true;
        }
        let v0 = w.header.vault.get();
        if w.with(|m, _| m.deposit_fresh_counterparty_backing_not_atomic(d, amt, exp)).is_ok() {
            had_provider = true;
            paid_in += w.header.vault.get() - v0;
        }
    }
    for i in 0..N {
        let amt = if std::env::var("LIENS").is_ok() { 1_000 + rng.below(60_000) as u128 } else { 1_000 + rng.below(1_000_000) as u128 };
        let v0 = w.header.vault.get();
        w.with(|m, accts| m.deposit_not_atomic(&mut PortfolioV16ViewMut::new(&mut accts[i]), amt)).unwrap();
        paid_in += w.header.vault.get() - v0;
    }
    w.shape("deposits");

    let ops = 20 + rng.below(40);
    let mm = cfg_mm;
    for _ in 0..ops {
        st.ops += 1;
        match rng.below(10) {
            0..=2 => {
                let a = rng.below(N as u64) as usize;
                let mut b = rng.below(N as u64) as usize;
                if a == b {
                    b = (b + 1) % N;
                }
                let asset = rng.below(ASSETS as u64) as usize;
                let span = if rng.below(2) == 0 { 50 } else { 2_000 };
                let units = 1 + rng.below(span) as i128;
                let q = if rng.below(2) == 0 { units } else { -units } * POS_SCALE as i128;
                let price = w.prices[asset];
                let r = w.with(|m, accts| {
                    let (x, y) = if a < b { let (l, r) = accts.split_at_mut(b); (&mut l[a], &mut r[0]) } else { let (l, r) = accts.split_at_mut(a); (&mut r[0], &mut l[b]) };
                    m.execute_trade_with_fee_loss_stale_scoped_not_atomic(
                        &mut PortfolioV16ViewMut::new(x),
                        &mut PortfolioV16ViewMut::new(y),
                        TradeRequestV16 { asset_index: asset as _, size_q: q, exec_price: price, fee_bps: 0 },
                    )
                });
                if r.is_ok() {
                    st.trades_ok += 1;
                }
                w.shape("trade");
            }
            3..=4 => {
                for _ in 0..1 + rng.below(10) {
                    w.step_price(&mut rng, cap);
                }
                w.shape("price");
                if std::env::var("LIENS").is_ok() {
                    // Settle everyone, then let each account try to add size on its gains.
                    for i in 0..N { w.crank(i, st); }
                    for i in 0..N {
                        let j = (i + 1 + rng.below(N as u64 - 1) as usize) % N;
                        let asset = rng.below(ASSETS as u64) as usize;
                        let price = w.prices[asset];
                        // Size so the initial margin needs capital plus some of the open gain.
                        let cap_i = w.accts[i].capital.get() as i128;
                        let pnl_i = w.accts[i].pnl.get().max(0);
                        let im = (2 * mm) as i128;
                        let budget = cap_i / 4 + pnl_i * (1 + rng.below(9) as i128) / 10;
                        let units = (budget * 10_000 / (im * price as i128)).max(1);
                        let q = if rng.below(2) == 0 { units } else { -units } * POS_SCALE as i128;
                        let _ = w.with(|m, accts| {
                            let (x, y) = if i < j { let (l, r) = accts.split_at_mut(j); (&mut l[i], &mut r[0]) } else { let (l, r) = accts.split_at_mut(i); (&mut r[0], &mut l[j]) };
                            m.execute_trade_with_fee_loss_stale_scoped_not_atomic(&mut PortfolioV16ViewMut::new(x), &mut PortfolioV16ViewMut::new(y), TradeRequestV16 { asset_index: asset as _, size_q: q, exec_price: price, fee_bps: 0 })
                        });
                        w.shape("gain trade");
                    }
                }
            }
            5..=6 => {
                let i = rng.below(N as u64) as usize;
                w.crank(i, st);
                w.shape("crank");
            }
            7 => {
                let i = rng.below(N as u64) as usize;
                let asset = rng.below(ASSETS as u64) as usize;
                let r = w.with(|m, accts| m.liquidate_account_not_atomic(&mut PortfolioV16ViewMut::new(&mut accts[i]), percolator::LiquidationRequestV16 { asset_index: asset }));
                if r.is_ok() {
                    st.liquidations_ok += 1;
                }
                w.shape("liquidate");
            }
            8 => {
                let i = rng.below(N as u64) as usize;
                let _ = w.with(|m, accts| m.convert_released_pnl_to_capital_not_atomic(&mut PortfolioV16ViewMut::new(&mut accts[i])));
                let amt = 1 + rng.below(50_000) as u128;
                let v0 = w.header.vault.get();
                let _ = w.with(|m, accts| m.withdraw_not_atomic(&mut PortfolioV16ViewMut::new(&mut accts[i]), amt));
                paid_out += v0 - w.header.vault.get();
                w.shape("convert/withdraw");
            }
            _ => {
                // Checkpoint: crank-order independence.
                st.checkpoints += 1;
                let mut a = w;
                let mut b = w;
                let mut o1: Vec<usize> = (0..N).collect();
                for k in (1..N).rev() {
                    o1.swap(k, rng.below(k as u64 + 1) as usize);
                }
                let o2: Vec<usize> = o1.iter().rev().cloned().collect();
                let mut sa = Stats::default();
                let mut sb = Stats::default();
                a.settle_all(&o1, &mut sa);
                b.settle_all(&o2, &mut sb);
                let (ea, da, ia, pa) = a.snapshot();
                let (eb, db, ib, pb) = b.snapshot();
                let va = a.header.vault.get();
                let vb = b.header.vault.get();
                if (ea.clone(), da.clone(), ia, pa) != (eb.clone(), db.clone(), ib, pb) {
                    let dust = va == vb
                        && ia == ib
                        && pa == pb
                        && ea.iter().zip(&eb).all(|(x, y)| (x - y).abs() <= 1)
                        && da.iter().zip(&db).all(|(x, y)| x[0].abs_diff(y[0]) <= 1 && x[1..] == y[1..]);
                    if dust {
                        st.order_dust += 1;
                    } else {
                        st.order_diffs += 1;
                        if va != vb || ia != ib || pa != pb || ea.iter().zip(&eb).any(|(x, y)| (x - y).abs() > 1) {
                            st.order_money += 1;
                            if std::env::var("SEEDS").is_ok() { println!("MSEED {seed:#x}"); }
                        }
                        if st.examples.len() < 3 {
                            st.examples.push(format!("seed {seed:#x}: order {o1:?} vs {o2:?}\n   eq {ea:?}\n   eq {eb:?}\n   dom {da:?}\n   dom {db:?}"));
                        }
                    }
                }
                w = if rng.below(2) == 0 { a } else { b };
                w.shape("checkpoint");
            }
        }
        if w.accts.iter().any(|a| a.capital.get() as i128 + a.pnl.get() < 0) {
            if !had_negative && std::env::var("DBG").is_ok() { println!("DBG first negative after op {} eq {:?} legs {:?}", st.ops, w.snapshot().0, w.accts.iter().map(|a| a.legs.iter().filter_map(|l| l.try_to_runtime().ok()).filter(|l| l.active).map(|l| (l.asset_index, l.side as u8)).collect::<Vec<_>>()).collect::<Vec<_>>()); }
            had_negative = true;
        }
        for a in 0..ASSETS {
            for c in [w.markets[a].engine.source_credit_long, w.markets[a].engine.source_credit_short] {
                let c = c.try_to_runtime().unwrap();
                if c.valid_liened_backing_num != 0 {
                    had_lien = true;
                }
            }
        }
    }
    if had_negative && std::env::var("SEEDS").is_ok() { println!("NSEED {seed:#x}"); }
    if had_negative {
        st.bankrupt_runs += 1;
    }
    st.lien_runs += had_lien as u64;
    st.lapse_runs += had_lapse as u64;

    // Wind-down.
    let order: Vec<usize> = (0..N).collect();
    w.settle_all(&order, st);
    st.deficit_total += w.accts.iter().map(|a| (a.capital.get() as i128 + a.pnl.get()).min(0)).sum::<i128>().abs();
    let dbg = std::env::var("DBG").is_ok();
    if dbg { println!("DBG pre-resolve vault {} c_tot {} ins {} eq {:?} cap {:?}", w.header.vault.get(), w.header.c_tot.get(), w.header.insurance.get(), w.snapshot().0, w.accts.iter().map(|a| a.capital.get()).collect::<Vec<_>>()); }
    let slot = w.slot;
    if w.with(|m, _| m.resolve_market_not_atomic(slot)).is_err() {
        st.resolve_fail += 1;
        return;
    }
    w.shape("resolve");
    let mut closed = [false; N];
    let close_round = |w: &mut World, closed: &mut [bool; N], paid_out: &mut u128, st: &mut Stats| {
        for i in 0..N {
            let v0 = w.header.vault.get();
            w.crank(i, st);
            let mut paid = 0u128;
            if !closed[i] {
                if let Ok(ResolvedCloseOutcomeV16::Closed { payout }) = w.with(|m, accts| m.close_resolved_account_not_atomic(&mut PortfolioV16ViewMut::new(&mut accts[i]), 0)) {
                    closed[i] = true;
                    paid += payout;
                }
            }
            if let Ok(t) = w.with(|m, accts| m.claim_resolved_payout_topup_not_atomic(&mut PortfolioV16ViewMut::new(&mut accts[i]))) {
                paid += t;
            }
            // Payouts are returned to the wrapper; count the larger of the returned amount and
            // the vault decrease (whichever the engine reports).
            if std::env::var("DBG").is_ok() && (paid > 0 || v0 != w.header.vault.get()) { println!("DBG acct {i} paid {paid} vault {} -> {} closed {}", v0, w.header.vault.get(), closed[i]); }
            *paid_out += paid.max(v0 - w.header.vault.get());
            w.shape("close");
        }
    };
    for _ in 0..6 {
        close_round(&mut w, &mut closed, &mut paid_out, st);
    }
    // Provider takes back what the engine says is surplus.
    for d in 0..2 * ASSETS {
        let s = w.with(|m, _| m.resolved_counterparty_backing_surplus(d)).unwrap_or(0);
        if s > 0 {
            let v0 = w.header.vault.get();
            let _ = w.with(|m, _| m.withdraw_resolved_counterparty_backing_surplus_not_atomic(d, s));
            paid_out += v0 - w.header.vault.get();
            w.shape("provider surplus");
        }
    }
    // Past every expiry.
    let mut real_expiry = max_expiry;
    for a in 0..ASSETS {
        for b in [w.markets[a].engine.backing_long, w.markets[a].engine.backing_short] {
            real_expiry = real_expiry.max(b.try_to_runtime().unwrap().expiry_slot);
        }
    }
    let late = real_expiry.max(w.slot) + 2;
    w.slot = late;
    let _ = w.with(|m, _| m.advance_resolved_slot_not_atomic(late));
    for d in 0..2 * ASSETS {
        let _ = w.with(|m, _| m.expire_source_backing_bucket_not_atomic(d, late));
    }
    for _ in 0..6 {
        close_round(&mut w, &mut closed, &mut paid_out, st);
    }
    for d in 0..2 * ASSETS {
        for _ in 0..2 {
            let v0 = w.header.vault.get();
            let _ = w.with(|m, _| m.withdraw_fresh_counterparty_backing_not_atomic(d, 1));
            let e = w.with(|m, _| m.resolved_counterparty_backing_surplus(d)).unwrap_or(0);
            if e > 0 {
                let _ = w.with(|m, _| m.withdraw_resolved_counterparty_backing_surplus_not_atomic(d, e));
            }
            let earn = w.header.backing_provider_earnings_total.get();
            if earn > 0 {
                let _ = w.with(|m, _| m.withdraw_backing_provider_earnings_not_atomic(d, earn));
            }
            paid_out += v0 - w.header.vault.get();
        }
    }
    if !closed.iter().all(|c| *c) {
        st.stuck_close += 1;
        if st.examples.len() < 6 {
            st.examples.push(format!("seed {seed:#x}: accounts not closed {closed:?}"));
        }
        return;
    }
    let mut retired = None;
    let mut last = String::new();
    for _ in 0..64 {
        match w.with(|m, _| m.advance_terminal_slab_not_atomic(late, 0)) {
            Ok(TerminalSlabOutcomeV16::ReadyToClose { retired: r }) => {
                if dbg { println!("DBG ready retired {r} vault {} c_tot {}", w.header.vault.get(), w.header.c_tot.get()); }
                retired = Some(r);
                break;
            }
            Ok(o) => last = format!("{o:?}"),
            Err(e) => { last = format!("Err {e:?}"); break }
        }
    }
    let Some(retired) = retired else {
        st.stuck_slab += 1;
        *st.crank_errors.entry(format!("slab: {last}")).or_default() += 1;
        if std::env::var("DBG").is_ok() {
            for d in 0..2 * ASSETS {
                let a = d / 2;
                let b = if d % 2 == 0 { w.markets[a].engine.backing_long } else { w.markets[a].engine.backing_short }.try_to_runtime().unwrap();
                println!("DBG stuck seed {seed:#x} slot {} domain {d}: {b:?}", w.header.current_slot.get());
            }
        }
        return;
    };
    // At ReadyToClose the wrapper removes `retired` from custody; what remains in the engine's
    // vault field after payouts is not meaningful at engine level, so conservation is
    // in == paid out + retired.
    let left = 0u128;
    let paid_out = paid_out + retired;
    if retired > 0 {
        st.retired_runs += 1;
        st.retired_total += retired;
        if !had_provider {
            st.leftover_runs += 1; // retired value in a run with no backing provider at all
            if st.examples.len() < 6 {
                st.examples.push(format!("seed {seed:#x}: retired {retired} with no provider"));
            }
        }
    }
    if paid_in != paid_out + left {
        st.conservation_breaks += 1;
        if st.examples.len() < 6 {
            st.examples.push(format!("seed {seed:#x}: in {paid_in} out {paid_out} (retired {retired}) diff {}", paid_in as i128 - paid_out as i128));
        }
    }
}

#[test]
fn money_and_order_fuzz() {
    let runs: u64 = std::env::var("RUNS").ok().and_then(|v| v.parse().ok()).unwrap_or(300);
    let seed0: u64 = std::env::var("SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0x5eed);
    let mut st = Stats::default();
    if let Ok(one) = std::env::var("ONE") {
        let seed = u64::from_str_radix(one.trim_start_matches("0x"), 16).unwrap();
        one_run(seed, &mut st);
        println!("ONE {one}: bankrupt {} liens {} order-diffs {} (money {}) retired {} conservation-breaks {} stuck {}/{}", st.bankrupt_runs, st.lien_runs, st.order_diffs, st.order_money, st.retired_total, st.conservation_breaks, st.stuck_close, st.stuck_slab);
        for e in &st.examples { println!("EXAMPLE {e}"); }
        return;
    }
    for k in 0..runs {
        one_run(seed0.wrapping_mul(6364136223846793005).wrapping_add(k.wrapping_mul(0x9e3779b97f4a7c15)), &mut st);
    }
    println!(
        "FUZZ runs {} ops {} trades {} liqs {} bankrupt-runs {} lien-runs {} lapse-runs {} | checkpoints {} ORDER-DIFFS {} (money {}) dust {} | resolve-fail {} STUCK-CLOSE {} STUCK-SLAB {} | retired-runs {} retired {} retired-without-provider {} CONSERVATION-BREAKS {}",
        st.runs, st.ops, st.trades_ok, st.liquidations_ok, st.bankrupt_runs, st.lien_runs, st.lapse_runs,
        st.checkpoints, st.order_diffs, st.order_money, st.order_dust, st.resolve_fail, st.stuck_close, st.stuck_slab,
        st.retired_runs, st.retired_total, st.leftover_runs, st.conservation_breaks
    );
    println!("FUZZ deficit {} retired {}", st.deficit_total, st.retired_total);
    println!("FUZZ crank errors {:?}", st.crank_errors);
    for e in &st.examples {
        println!("EXAMPLE {e}");
    }
}
