use super::plan::{plan_unrolled_stream, StreamPlan};
use super::{fsv_dir, load_calibration_proof, trace_verifier, Trace};
use full_statement_verifier::host_utils::cost_model::census::{
    CensusVec, CENSUS_DIMS, NUM_CENSUS_DIMS, NUM_FAMILY_DIMS,
};
use full_statement_verifier::host_utils::cost_model::{compiled_circuits, CircuitId};
use std::collections::BTreeMap;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

pub fn trace_fixture(name: &str, program: FsvProgram) -> (Trace, StreamPlan) {
    let (bin, text) = full_statement_verifier::host_utils::load_fsv_program(
        fsv_dir(),
        program,
        BlakeMode::Compression,
    );
    let (setups, proof) = load_calibration_proof(name);
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
    let plan = plan_unrolled_stream(&setups, &proof, program);
    assert_eq!(
        plan.total_words,
        stream.len(),
        "{name}: stream plan disagrees with the stream"
    );
    let t = trace_verifier(&bin, &text, stream);
    (t, plan)
}

/// Census of one circuit's region of the ND stream, from its count word to
/// the next region's count word (or the PoW word).
pub struct RegionCensus {
    pub circuit: CircuitId,
    pub count: usize,
    pub region: CensusVec,
    /// Count word to the first proof's first word; the whole region if empty.
    pub head: CensusVec,
    /// First word of each proof to the next proof's first word. The last
    /// proof has no span: its work and the region tail stay in the residual.
    pub spans: Vec<CensusVec>,
}

pub struct CensusCalibration {
    pub total: CensusVec,
    pub regions: Vec<RegionCensus>,
}

pub fn calibrate_census_fixture(name: &str, program: FsvProgram) -> CensusCalibration {
    let (t, plan) = trace_fixture(name, program);
    calibrate_census(&t, &plan)
}

pub fn calibrate_census(trace: &Trace, plan: &StreamPlan) -> CensusCalibration {
    let census = |from: usize, to: usize| -> CensusVec {
        core::array::from_fn(|d| trace.census_marks[to][d] - trace.census_marks[from][d])
    };
    let regions = plan
        .regions
        .iter()
        .map(|r| RegionCensus {
            circuit: r.circuit,
            count: r.proof_first_words.len(),
            region: census(r.count_word, r.end_word),
            head: census(
                r.count_word,
                r.proof_first_words.first().copied().unwrap_or(r.end_word),
            ),
            spans: r
                .proof_first_words
                .windows(2)
                .map(|w| census(w[0], w[1]))
                .collect(),
        })
        .collect();
    CensusCalibration {
        total: trace.total_census,
        regions,
    }
}

/// Per-proof price of each circuit: the mean of all its spans across one
/// program's fixtures, so every observed proof weighs the same. A circuit
/// without a span gets no price.
pub fn pooled_prices<'a>(
    cals: impl IntoIterator<Item = &'a CensusCalibration>,
) -> BTreeMap<CircuitId, CensusVec> {
    let mut sums: BTreeMap<CircuitId, (CensusVec, u64)> = BTreeMap::new();
    for cal in cals {
        for r in &cal.regions {
            for span in &r.spans {
                let (sum, n) = sums.entry(r.circuit).or_insert(([0; NUM_CENSUS_DIMS], 0));
                for d in 0..NUM_CENSUS_DIMS {
                    sum[d] += span[d];
                }
                *n += 1;
            }
        }
    }
    sums.into_iter()
        .map(|(circuit, (sum, n))| (circuit, sum.map(|s| (s + n / 2) / n)))
        .collect()
}

/// Census dims followed by total cycles (the family dims' sum).
pub const NUM_ROWS: usize = NUM_CENSUS_DIMS + 1;
pub const TOTAL_ROW: usize = NUM_CENSUS_DIMS;

/// Original relative allowance, applied to the deterministic lower component.
pub fn gate_budget(row: usize, measured: u64) -> u64 {
    if row < NUM_FAMILY_DIMS {
        (measured / 1000).max(8)
    } else if row < NUM_CENSUS_DIMS {
        (measured / 2000).max(8)
    } else {
        measured / 2000
    }
}

/// Empirical per-proof envelope for one verifier program. Centre every span on
/// its own circuit's rounded mean before taking the maximum absolute deviation
/// in each row. The total-cycle row is measured directly, not the sum of the
/// dimensional envelopes. No independence or cancellation is assumed.
///
/// At least one circuit must have two observed spans. A single i&t span cannot
/// establish zero variance: it shares the program-row envelope measured from
/// the other repeated proofs. Every circuit still needs its own measured price.
/// This covers observed spread; it is not a statistical future-tail guarantee.
pub fn observed_spread<'a>(
    cals: impl IntoIterator<Item = &'a CensusCalibration>,
    prices: &BTreeMap<CircuitId, CensusVec>,
) -> Option<[u64; NUM_ROWS]> {
    let mut counts = BTreeMap::<CircuitId, usize>::new();
    let mut spread = [0; NUM_ROWS];
    for cal in cals {
        for r in &cal.regions {
            for span in &r.spans {
                *counts.entry(r.circuit).or_default() += 1;
                let price = &prices[&r.circuit];
                for d in 0..NUM_CENSUS_DIMS {
                    spread[d] = spread[d].max(span[d].abs_diff(price[d]));
                }
                let actual: u64 = span[..NUM_FAMILY_DIMS].iter().sum();
                let mean: u64 = price[..NUM_FAMILY_DIMS].iter().sum();
                spread[TOTAL_ROW] = spread[TOTAL_ROW].max(actual.abs_diff(mean));
            }
        }
    }
    counts.values().any(|n| *n >= 2).then_some(spread)
}

/// For N proofs and observed row envelope delta, V = N * delta bounds their
/// combined deviations without assuming cancellation. Apply the original
/// relative allowance to max(T - V, 0), then add V. Rows with zero observed
/// spread retain their original allowance exactly, including its small floor.
fn budget_parts(row: usize, total: u64, proofs: u64, delta: u64) -> (i64, i64) {
    let spread = proofs.checked_mul(delta).expect("proof spread overflow");
    let deterministic = gate_budget(row, total.saturating_sub(spread));
    let _: i64 = deterministic
        .checked_add(spread)
        .expect("budget overflow")
        .try_into()
        .expect("signed budget overflow");
    (
        deterministic
            .try_into()
            .expect("deterministic budget overflow"),
        spread.try_into().expect("spread budget overflow"),
    )
}

fn row_label(row: usize) -> String {
    if row < NUM_CENSUS_DIMS {
        format!("{:?}", CENSUS_DIMS[row])
    } else {
        "total".to_owned()
    }
}

/// One fixture's measured total split as `total = outside + structural +
/// pricing + Σ n·v`: work outside every region, region heads (whole empty
/// regions), and the signed residual of the nonempty regions' proofs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrefitRow {
    pub total: i64,
    pub budget: i64,
    pub deterministic_budget: i64,
    pub spread_budget: i64,
    pub outside: i64,
    pub structural: i64,
    pub pricing: i64,
}

impl PrefitRow {
    /// The C0 this fixture needs for an exact estimate.
    pub fn intercept(&self) -> i64 {
        self.outside + self.structural + self.pricing
    }
    pub fn margin(&self) -> i64 {
        self.budget - self.pricing.abs()
    }
}

/// `Err` lists the circuits with proofs but no price.
pub fn prefit_rows(
    cal: &CensusCalibration,
    prices: &BTreeMap<CircuitId, CensusVec>,
    spread: &[u64; NUM_ROWS],
) -> Result<[PrefitRow; NUM_ROWS], Vec<CircuitId>> {
    let unpriced: Vec<_> = cal
        .regions
        .iter()
        .filter(|r| r.count > 0 && !prices.contains_key(&r.circuit))
        .map(|r| r.circuit)
        .collect();
    if !unpriced.is_empty() {
        return Err(unpriced);
    }
    let proofs: u64 = cal.regions.iter().map(|r| r.count as u64).sum();
    let mut rows = [PrefitRow::default(); NUM_ROWS];
    for d in 0..NUM_CENSUS_DIMS {
        let total = cal.total[d] as i64;
        let (deterministic_budget, spread_budget) =
            budget_parts(d, cal.total[d], proofs, spread[d]);
        let mut row = PrefitRow {
            total,
            budget: deterministic_budget + spread_budget,
            deterministic_budget,
            spread_budget,
            outside: total,
            ..Default::default()
        };
        for r in &cal.regions {
            row.outside -= r.region[d] as i64;
            row.structural += r.head[d] as i64;
            if r.count > 0 {
                row.pricing += r.region[d] as i64
                    - r.head[d] as i64
                    - r.count as i64 * prices[&r.circuit][d] as i64;
            }
        }
        rows[d] = row;
    }
    let family = &rows[..NUM_FAMILY_DIMS];
    let total: i64 = family.iter().map(|r| r.total).sum();
    let (deterministic_budget, spread_budget) =
        budget_parts(TOTAL_ROW, total as u64, proofs, spread[TOTAL_ROW]);
    rows[TOTAL_ROW] = PrefitRow {
        total,
        budget: deterministic_budget + spread_budget,
        deterministic_budget,
        spread_budget,
        outside: family.iter().map(|r| r.outside).sum(),
        structural: family.iter().map(|r| r.structural).sum(),
        pricing: family.iter().map(|r| r.pricing).sum(),
    };
    Ok(rows)
}

/// The premises of an affine fit for one verifier program, checked before
/// any C0 is chosen: every present circuit priced, each fixture's pricing
/// residual strictly inside its variance-aware budget, repeated-span evidence
/// for the program-row envelope, and one nonnegative C0 within every budget.
pub struct ProgramPrefit {
    pub prices: BTreeMap<CircuitId, CensusVec>,
    pub spread: Option<[u64; NUM_ROWS]>,
    pub fixtures: Vec<(String, Result<[PrefitRow; NUM_ROWS], Vec<CircuitId>>)>,
    /// Pricing residual with the fixture's own spans left out (informational).
    pub held_out: Vec<Option<[i64; NUM_ROWS]>>,
}

impl ProgramPrefit {
    /// Acceptance uses the frozen reference envelope, rather than learning a
    /// more permissive allowance from the input under test. Missing measured
    /// repetition evidence and missing circuit prices still fail closed.
    pub fn with_reference_spread(
        cals: &[(&str, &CensusCalibration)],
        reference: [u64; NUM_ROWS],
    ) -> Self {
        let mut prefit = Self::new(cals);
        prefit.fixtures = cals
            .iter()
            .map(|(name, cal)| {
                (
                    name.to_string(),
                    prefit_rows(cal, &prefit.prices, &reference),
                )
            })
            .collect();
        prefit.spread = prefit.spread.map(|_| reference);
        prefit
    }

    pub fn new(cals: &[(&str, &CensusCalibration)]) -> Self {
        let prices = pooled_prices(cals.iter().map(|(_, c)| *c));
        let spread = observed_spread(cals.iter().map(|(_, c)| *c), &prices);
        let envelope = spread.unwrap_or([0; NUM_ROWS]);
        let fixtures = cals
            .iter()
            .map(|(name, cal)| (name.to_string(), prefit_rows(cal, &prices, &envelope)))
            .collect();
        let held_out = (0..cals.len())
            .map(|i| {
                let others = pooled_prices(
                    cals.iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, (_, c))| *c),
                );
                prefit_rows(cals[i].1, &others, &envelope)
                    .ok()
                    .map(|rows| rows.map(|r| r.pricing))
            })
            .collect();
        Self {
            prices,
            spread,
            fixtures,
            held_out,
        }
    }

    /// `[max(K − B), min(K + B)]` over the fixtures with rows.
    pub fn interval(&self, row: usize) -> (i64, i64) {
        self.fixtures
            .iter()
            .filter_map(|(_, rows)| rows.as_ref().ok())
            .fold((i64::MIN, i64::MAX), |(lo, hi), rows| {
                let r = &rows[row];
                (
                    lo.max(r.intercept() - r.budget),
                    hi.min(r.intercept() + r.budget),
                )
            })
    }

    pub fn failures(&self) -> Vec<String> {
        let mut out = Vec::new();
        if self.spread.is_none() {
            out.push("no circuit has two observed spans to measure proof spread".to_owned());
        }
        for (name, rows) in &self.fixtures {
            match rows {
                Err(unpriced) => {
                    out.push(format!("{name}: no repeated-proof price for {unpriced:?}"))
                }
                Ok(rows) => {
                    for (row, r) in rows.iter().enumerate() {
                        if r.margin() <= 0 {
                            out.push(format!(
                                "{name} {}: pricing residual {:+} not inside budget {} \
                                 (deterministic {} + spread {})",
                                row_label(row),
                                r.pricing,
                                r.budget,
                                r.deterministic_budget,
                                r.spread_budget,
                            ));
                        }
                    }
                }
            }
        }
        if !self.fixtures.is_empty() && self.fixtures.iter().all(|(_, rows)| rows.is_ok()) {
            for row in 0..NUM_ROWS {
                let (lo, hi) = self.interval(row);
                if lo > hi || hi < 0 {
                    out.push(format!(
                        "{}: no nonnegative C0 within every fixture's budget ({lo}..={hi})",
                        row_label(row)
                    ));
                }
            }
            let (total_lo, total_hi) = self.interval(TOTAL_ROW);
            let (family_lo, family_hi) = (0..NUM_FAMILY_DIMS).fold((0, 0), |(lo, hi), d| {
                let (dim_lo, dim_hi) = self.interval(d);
                (lo + dim_lo.max(0), hi + dim_hi)
            });
            if family_lo > total_hi || family_hi < total_lo {
                out.push(format!(
                    "family C0 sum {family_lo}..={family_hi} cannot meet total interval \
                     {total_lo}..={total_hi}"
                ));
            }
        }
        out
    }

    /// Start at each interval's midpoint, raised to zero, then keep the family sum
    /// inside the total-cycle interval too. Per-dim spread maxima can occur in
    /// different proofs; their sum is not the observed total-cycle envelope.
    pub fn c0(&self) -> CensusVec {
        let failures = self.failures();
        assert!(failures.is_empty(), "cannot fit: {failures:?}");
        let mut c0: CensusVec = core::array::from_fn(|d| {
            let (lo, hi) = self.interval(d);
            assert!(lo <= hi && hi >= 0, "{}: no C0", row_label(d));
            (lo + (hi - lo) / 2).max(lo.max(0)) as u64
        });
        let sum: i64 = c0[..NUM_FAMILY_DIMS].iter().map(|v| *v as i64).sum();
        let (lo, hi) = self.interval(TOTAL_ROW);
        let mut remaining = sum.clamp(lo.max(0), hi) - sum;
        for (d, value) in c0[..NUM_FAMILY_DIMS].iter_mut().enumerate() {
            let (lo, hi) = self.interval(d);
            let current = *value as i64;
            let adjustment = remaining.clamp(lo.max(0) - current, hi - current);
            *value = (current + adjustment) as u64;
            remaining -= adjustment;
        }
        assert_eq!(remaining, 0, "family C0 sum must meet the total interval");
        c0
    }

    pub fn report(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "per-proof allowance envelope: {:?}\n",
            self.spread
        ));
        for (i, (name, rows)) in self.fixtures.iter().enumerate() {
            let rows = match rows {
                Ok(rows) => rows,
                Err(unpriced) => {
                    out.push_str(&format!(
                        "{name}: unavailable, no repeated-proof price for {unpriced:?}\n"
                    ));
                    continue;
                }
            };
            for (row, r) in rows.iter().enumerate() {
                let held_out = self.held_out[i]
                    .map(|j| format!("{:+}", j[row]))
                    .unwrap_or_else(|| "n/a".to_owned());
                out.push_str(&format!(
                    "{name} {}: T={} B={} O={} H={} J={:+} margin={} K={} \
                     J_held_out={held_out} B_det={} V={}\n",
                    row_label(row),
                    r.total,
                    r.budget,
                    r.outside,
                    r.structural,
                    r.pricing,
                    r.margin(),
                    r.intercept(),
                    r.deterministic_budget,
                    r.spread_budget,
                ));
            }
        }
        if self.fixtures.iter().all(|(_, rows)| rows.is_ok()) {
            for row in 0..NUM_ROWS {
                let (lo, hi) = self.interval(row);
                out.push_str(&format!("C0 {}: {lo}..={hi}\n", row_label(row)));
            }
        }
        out
    }
}

/// Every span, and each nonempty region's residual split into the spanned
/// proofs and the last proof plus the region tail.
pub fn render_regions(
    name: &str,
    cal: &CensusCalibration,
    prices: &BTreeMap<CircuitId, CensusVec>,
) -> String {
    let mut out = String::new();
    for r in cal.regions.iter().filter(|r| r.count > 0) {
        out.push_str(&format!(
            "{name} {:?} n={} region={:?} head={:?}\n",
            r.circuit, r.count, r.region, r.head
        ));
        for span in &r.spans {
            out.push_str(&format!("{name} {:?} span={span:?}\n", r.circuit));
        }
        if let Some(v) = prices.get(&r.circuit) {
            let inner: [i64; NUM_CENSUS_DIMS] =
                core::array::from_fn(|d| r.spans.iter().map(|s| s[d] as i64 - v[d] as i64).sum());
            let last: [i64; NUM_CENSUS_DIMS] = core::array::from_fn(|d| {
                r.region[d] as i64
                    - r.head[d] as i64
                    - r.spans.iter().map(|s| s[d] as i64).sum::<i64>()
                    - v[d] as i64
            });
            out.push_str(&format!(
                "{name} {:?} price={v:?} spanned_residual={inner:?} last_residual={last:?}\n",
                r.circuit
            ));
        }
    }
    out
}

pub struct PooledCensus {
    pub v: BTreeMap<CircuitId, CensusVec>,
    pub c0: Vec<(FsvProgram, CensusVec)>,
    pub spread: [u64; NUM_ROWS],
}

/// Independent coarse check for incompatible circuit means. The binding
/// acceptance and pre-fit allowances use the measured proof-spread envelope.
const CENSUS_REL_DIV: u64 = 64;
const CENSUS_ABS_FLOOR: u64 = 8;

pub fn pool_census(cals: &[(&str, FsvProgram, CensusCalibration)]) -> PooledCensus {
    assert!(!cals.is_empty(), "need at least one calibration fixture");
    let program = cals[0].1;
    assert!(
        cals.iter().all(|(_, p, _)| *p == program),
        "pool one verifier program at a time"
    );
    let named: Vec<_> = cals.iter().map(|(name, _, c)| (*name, c)).collect();
    let prefit = ProgramPrefit::new(&named);
    let failures = prefit.failures();
    assert!(
        failures.is_empty(),
        "{program:?}: the fit's premises fail\n{}",
        failures.join("\n")
    );

    for (circuit, v) in &prefit.prices {
        let means: Vec<CensusVec> = cals
            .iter()
            .filter_map(|(_, _, c)| {
                let spans: Vec<_> = c
                    .regions
                    .iter()
                    .filter(|r| r.circuit == *circuit)
                    .flat_map(|r| &r.spans)
                    .collect();
                let n = spans.len() as u64;
                (n > 0).then(|| {
                    core::array::from_fn(|d| (spans.iter().map(|s| s[d]).sum::<u64>() + n / 2) / n)
                })
            })
            .collect();
        for d in 0..NUM_CENSUS_DIMS {
            let lo = means.iter().map(|m| m[d]).min().unwrap();
            let hi = means.iter().map(|m| m[d]).max().unwrap();
            assert!(
                hi - lo <= (hi / CENSUS_REL_DIV).max(CENSUS_ABS_FLOOR),
                "{circuit:?} census dim {d} differs by more than the pooling bound across \
                 fixtures (min {lo}, max {hi}, pooled {})",
                v[d]
            );
        }
    }

    PooledCensus {
        c0: vec![(program, prefit.c0())],
        spread: prefit.spread.expect("measured proof spread"),
        v: prefit.prices,
    }
}

pub fn render_census_tables(pooled: &PooledCensus) -> String {
    let fmt_vec = |v: &CensusVec| {
        let inner: Vec<String> = v.iter().map(|x| x.to_string()).collect();
        format!("[{}]", inner.join(", "))
    };
    let mut out = String::new();
    for (program, c0) in &pooled.c0 {
        out.push_str(&format!(
            "    (
        FsvProgram::{program:?},
        BlakeMode::Compression,
        CensusTable {{
            c0: {},
            per_proof_spread: {:?},
            v: &[
",
            fmt_vec(c0),
            pooled.spread,
        ));
        for circuit in compiled_circuits(*program) {
            if let Some(cost) = pooled.v.get(&circuit) {
                let id = match circuit {
                    CircuitId::Riscv(k) => format!("CircuitId::Riscv({k})"),
                    CircuitId::InitsAndTeardowns => "CircuitId::InitsAndTeardowns".to_owned(),
                    CircuitId::Delegation(k) => format!("CircuitId::Delegation({k})"),
                };
                out.push_str(&format!(
                    "                ({id}, {}),
",
                    fmt_vec(cost)
                ));
            }
        }
        out.push_str(
            "            ],
        },
    ),
",
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const CIRCUIT: CircuitId = CircuitId::Riscv(3);
    const DIM: usize = 2;

    /// One `CIRCUIT` region priced in `DIM` only; every other dim measures 0.
    fn fixture(spans: &[u64], last: u64, outside: u64) -> CensusCalibration {
        let at = |v: u64| {
            let mut out = [0; NUM_CENSUS_DIMS];
            out[DIM] = v;
            out
        };
        let head = 3;
        let region = head + spans.iter().sum::<u64>() + last;
        CensusCalibration {
            total: at(outside + region),
            regions: vec![RegionCensus {
                circuit: CIRCUIT,
                count: spans.len() + 1,
                region: at(region),
                head: at(head),
                spans: spans.iter().map(|s| at(*s)).collect(),
            }],
        }
    }

    fn prefit(cals: &[CensusCalibration]) -> ProgramPrefit {
        let named: Vec<_> = cals.iter().map(|c| ("f", c)).collect();
        ProgramPrefit::new(&named)
    }

    /// Three families exchange proof work, but the total proof cost is fixed.
    /// Each input puts its outside work in a different family.
    fn anticorrelated_fixtures(amplitude: u64) -> Vec<CensusCalibration> {
        (0..3)
            .map(|high| {
                let spans = (0..3)
                    .map(|s| {
                        let mut v = [0; NUM_CENSUS_DIMS];
                        v[..3].fill(100_000);
                        v[s] += amplitude;
                        v[(s + 1) % 3] -= amplitude;
                        v
                    })
                    .collect();
                let mut region = [0; NUM_CENSUS_DIMS];
                region[..3].fill(400_000);
                let mut total = region;
                for (d, value) in total[..3].iter_mut().enumerate() {
                    *value += if d == high { 5_000 } else { 1_000 };
                }
                CensusCalibration {
                    total,
                    regions: vec![RegionCensus {
                        circuit: CIRCUIT,
                        count: 4,
                        region,
                        head: [0; NUM_CENSUS_DIMS],
                        spans,
                    }],
                }
            })
            .collect()
    }

    #[test]
    fn c0_respects_the_total_when_family_variations_cancel() {
        let cals = anticorrelated_fixtures(800);
        let p = prefit(&cals);
        assert!(p.failures().is_empty(), "{:?}", p.failures());
        let c0 = p.c0();
        let total_c0: u64 = c0[..NUM_FAMILY_DIMS].iter().sum();
        for (_, rows) in &p.fixtures {
            let rows = rows.as_ref().unwrap();
            for (d, row) in rows.iter().enumerate() {
                let intercept = if d == TOTAL_ROW { total_c0 } else { c0[d] };
                assert!((intercept as i64 - row.intercept()).abs() <= row.budget);
            }
        }
    }

    #[test]
    fn incompatible_family_sum_fails_before_fitting() {
        let p = prefit(&anticorrelated_fixtures(400));
        for d in 0..NUM_ROWS {
            let (lo, hi) = p.interval(d);
            assert!(lo <= hi && hi >= 0, "each separate interval is feasible");
        }
        assert!(p.failures().iter().any(|f| f.contains("family C0 sum")));
        assert!(std::panic::catch_unwind(|| p.c0()).is_err());
    }

    #[test]
    fn measured_spread_covers_singleton_variation() {
        // Repeated proof spans differ by +/-400 around their circuit mean.
        // The singleton's +450 residual fails the old relative budget, but is
        // inside one measured proof envelope plus the original allowance.
        let cals = [
            fixture(&[99_600, 100_400], 100_000, 5_000),
            fixture(&[], 100_450, 5_000),
        ];
        let p = prefit(&cals);
        assert!(p.failures().is_empty(), "{:?}", p.failures());
        let rows = p.fixtures[1].1.as_ref().unwrap();
        assert_eq!(rows[DIM].spread_budget, 400);
        assert_eq!(rows[TOTAL_ROW].budget, 452);
    }

    #[test]
    fn one_span_does_not_establish_zero_variance() {
        let p = prefit(&[fixture(&[100_000], 100_000, 5_000)]);
        assert!(p.spread.is_none());
        assert!(p
            .failures()
            .iter()
            .any(|f| f.contains("two observed spans")));
        assert!(std::panic::catch_unwind(|| p.c0()).is_err());
    }

    #[test]
    fn acceptance_does_not_enlarge_its_frozen_reference_envelope() {
        let cals = [
            fixture(&[99_600, 100_400], 100_000, 5_000),
            fixture(&[], 100_450, 5_000),
        ];
        let named: Vec<_> = cals.iter().map(|c| ("f", c)).collect();
        assert!(ProgramPrefit::new(&named).failures().is_empty());
        let fixed = ProgramPrefit::with_reference_spread(&named, [0; NUM_ROWS]);
        assert!(fixed
            .failures()
            .iter()
            .any(|f| f.contains("not inside budget")));
        assert!(std::panic::catch_unwind(|| fixed.c0()).is_err());
    }

    #[test]
    fn constant_rows_retain_the_original_allowance() {
        let cals = [fixture(&[100_000, 100_000], 100_000, 5_000)];
        let p = prefit(&cals);
        assert_eq!(p.spread, Some([0; NUM_ROWS]));
        let rows = p.fixtures[0].1.as_ref().unwrap();
        for (d, row) in rows.iter().enumerate() {
            assert_eq!(row.budget, gate_budget(d, row.total as u64) as i64);
            assert_eq!(row.spread_budget, 0);
        }
    }

    #[test]
    fn total_spread_is_not_the_sum_of_dimensional_maxima() {
        let mut cal = fixture(&[100_000, 100_000], 100_000, 0);
        cal.regions[0].spans[0][0] = 99_600;
        cal.regions[0].spans[0][DIM] = 100_400;
        cal.regions[0].spans[1][0] = 100_400;
        cal.regions[0].spans[1][DIM] = 99_600;
        let spread = observed_spread([&cal], &pooled_prices([&cal])).unwrap();
        assert_eq!(spread[0], 400);
        assert_eq!(spread[DIM], 400);
        assert_eq!(spread[TOTAL_ROW], 0);
    }

    #[test]
    fn spread_centres_each_circuit_before_taking_the_envelope() {
        let first = fixture(&[99_600, 100_400], 100_000, 0);
        let mut other = fixture(&[199_900, 200_100], 200_000, 0);
        other.regions[0].circuit = CircuitId::Riscv(2);
        let cals = [&first, &other];
        let spread = observed_spread(cals, &pooled_prices(cals)).unwrap();
        assert_eq!(spread[DIM], 400);
    }

    #[test]
    fn residual_outside_the_measured_allowance_is_rejected() {
        let cals = [
            fixture(&[99_600, 100_400], 100_000, 5_000),
            fixture(&[], 101_000, 5_000),
        ];
        let p = prefit(&cals);
        assert!(p.failures().iter().any(|f| f.contains("not inside budget")));
        assert!(std::panic::catch_unwind(|| p.c0()).is_err());
    }

    #[test]
    fn prices_weigh_every_span_equally() {
        let cals = [
            fixture(&[100_000, 100_002], 100_000, 0),
            fixture(&[100_010], 100_000, 0),
        ];
        assert_eq!(pooled_prices(&cals)[&CIRCUIT][DIM], 100_004);
    }

    #[test]
    fn singleton_without_a_span_is_unpriced() {
        let p = prefit(&[fixture(&[], 100_000, 5_000)]);
        assert!(p.prices.is_empty());
        assert_eq!(p.fixtures[0].1, Err(vec![CIRCUIT]));
        assert!(p
            .failures()
            .iter()
            .any(|f| f.contains("no repeated-proof price")));
    }

    #[test]
    fn a_spread_envelope_does_not_supply_a_missing_circuit_price() {
        let repeated = fixture(&[99_600, 100_400], 100_000, 0);
        let mut singleton = fixture(&[], 100_000, 0);
        singleton.regions[0].circuit = CircuitId::Riscv(2);
        let p = prefit(&[repeated, singleton]);
        assert!(p.spread.is_some());
        assert_eq!(p.fixtures[1].1, Err(vec![CircuitId::Riscv(2)]));
        assert!(std::panic::catch_unwind(|| p.c0()).is_err());
    }

    #[test]
    fn split_reconstructs_the_total() {
        let cal = fixture(&[100_000, 100_100], 100_050, 5_000);
        let prices = pooled_prices([&cal]);
        let spread = observed_spread([&cal], &prices).unwrap();
        let rows = prefit_rows(&cal, &prices, &spread).unwrap();
        let r = rows[DIM];
        assert_eq!(r.outside + r.structural + r.pricing + 3 * 100_050, r.total);
        assert_eq!((r.outside, r.structural, r.pricing), (5_000, 3, 0));
        assert_eq!(rows[TOTAL_ROW].total, r.total);
    }

    #[test]
    fn residual_at_the_budget_is_rejected() {
        // J = j. The total row binds: B = 305_155 / 2000 = 152.
        let at = |j: u64| prefit(&[fixture(&[100_000, 100_000], 100_000 + j, 5_000)]);
        assert!(at(151).failures().is_empty());
        assert!(at(152)
            .failures()
            .iter()
            .any(|f| f.starts_with("f total") && f.contains("not inside budget")));
        let measured = prefit(&[
            fixture(&[99_600, 100_400], 100_000, 5_000),
            fixture(&[], 100_452, 5_000),
        ]);
        let row = measured.fixtures[1].1.as_ref().unwrap()[TOTAL_ROW];
        assert_eq!(row.pricing, row.budget);
        assert!(measured
            .failures()
            .iter()
            .any(|f| f.starts_with("f total") && f.contains("not inside budget")));
    }

    #[test]
    fn conflicting_intercepts_are_rejected() {
        let small = fixture(&[100_000], 100_000, 5_000);
        let large = fixture(&[100_000; 3], 100_000, 5_800);
        let failures = prefit(&[small, large]).failures();
        assert!(failures
            .iter()
            .any(|f| f.starts_with("Riscv(3)") && f.contains("no nonnegative C0")));
    }

    #[test]
    fn negative_intercept_interval_is_rejected() {
        // J = -2_000, so K = 3 - 2_000 and K + b < 0.
        let p = prefit(&[fixture(&[100_000], 98_000, 0)]);
        assert!(p.failures().iter().any(|f| f.contains("no nonnegative C0")));
    }

    #[test]
    fn c0_fits_every_fixture_and_keeps_zero_dims() {
        let cals = [
            fixture(&[100_000], 100_040, 5_000),
            fixture(&[100_000; 3], 99_950, 5_010),
        ];
        let p = prefit(&cals);
        assert!(p.failures().is_empty(), "{:?}", p.failures());
        let c0 = p.c0();
        for cal in &cals {
            let n = cal.regions[0].count as u64;
            let estimate = c0[DIM] + n * p.prices[&CIRCUIT][DIM];
            assert!(estimate.abs_diff(cal.total[DIM]) <= gate_budget(DIM, cal.total[DIM]));
        }
        for d in (0..NUM_CENSUS_DIMS).filter(|d| *d != DIM) {
            assert_eq!(c0[d], 0);
            assert_eq!(p.prices[&CIRCUIT][d], 0);
        }
    }
}
