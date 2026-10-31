use super::plan::{plan_unrolled_stream, StreamPlan};
use super::{fsv_dir, load_calibration_proof, trace_verifier, Trace};
use full_statement_verifier::host_utils::cost_model::census::{
    CensusVec, NUM_CENSUS_DIMS, NUM_FAMILY_DIMS,
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
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(
        &setups,
        &proof,
        BlakeMode::Compression,
    );
    let plan = plan_unrolled_stream(&setups, &proof, program);
    assert_eq!(
        plan.total_words,
        stream.len(),
        "{name}: stream plan disagrees with the stream"
    );
    let t = trace_verifier(&bin, &text, stream);
    (t, plan)
}

pub struct RegionCensus {
    pub circuit: CircuitId,
    pub count: usize,
    pub spans: Vec<CensusVec>,
}

pub struct CensusCalibration {
    pub total: CensusVec,
    pub regions: Vec<RegionCensus>,
}

pub fn calibrate_census_fixture(name: &str, program: FsvProgram) -> CensusCalibration {
    let (trace, plan) = trace_fixture(name, program);
    let regions = plan
        .regions
        .iter()
        .map(|region| RegionCensus {
            circuit: region.circuit,
            count: region.proof_first_words.len(),
            spans: region
                .proof_first_words
                .windows(2)
                .map(|words| {
                    core::array::from_fn(|d| {
                        trace.census_marks[words[1]][d] - trace.census_marks[words[0]][d]
                    })
                })
                .collect(),
        })
        .collect();
    CensusCalibration {
        total: trace.total_census,
        regions,
    }
}

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

pub const NUM_ROWS: usize = NUM_CENSUS_DIMS + 1;
pub const TOTAL_ROW: usize = NUM_CENSUS_DIMS;

/// Original relative allowance on the deterministic component, plus N times
/// the measured maximum per-proof deviation. Total cycles have their own row.
pub fn gate_budget(row: usize, measured: u64, proofs: u64, delta: u64) -> u64 {
    let spread = proofs * delta;
    let deterministic = measured.saturating_sub(spread);
    let relative = if row < NUM_FAMILY_DIMS {
        (deterministic / 1000).max(8)
    } else if row < NUM_CENSUS_DIMS {
        (deterministic / 2000).max(8)
    } else {
        deterministic / 2000
    };
    relative + spread
}

/// Centre spans on each circuit's rounded mean. Measure total deviations
/// separately: per-dimension maxima can occur in different proofs.
fn observed_spread(
    cals: &[CensusCalibration],
    prices: &BTreeMap<CircuitId, CensusVec>,
) -> [u64; NUM_ROWS] {
    let mut spread = [0; NUM_ROWS];
    for cal in cals {
        for region in &cal.regions {
            for span in &region.spans {
                let price = &prices[&region.circuit];
                for d in 0..NUM_CENSUS_DIMS {
                    spread[d] = spread[d].max(span[d].abs_diff(price[d]));
                }
                let actual: u64 = span[..NUM_FAMILY_DIMS].iter().sum();
                let mean: u64 = price[..NUM_FAMILY_DIMS].iter().sum();
                spread[TOTAL_ROW] = spread[TOTAL_ROW].max(actual.abs_diff(mean));
            }
        }
    }
    spread
}

pub struct PooledCensus {
    pub v: BTreeMap<CircuitId, CensusVec>,
    pub c0: CensusVec,
    pub spread: [u64; NUM_ROWS],
}

pub fn pool_census(cals: &[CensusCalibration]) -> PooledCensus {
    assert!(!cals.is_empty(), "need at least one calibration fixture");
    let prices = pooled_prices(cals);
    let spread = observed_spread(cals, &prices);
    let rows: Vec<[(i64, i64); NUM_ROWS]> = cals
        .iter()
        .map(|cal| {
            let proofs = cal.regions.iter().map(|r| r.count as u64).sum();
            let mut variable = [0; NUM_ROWS];
            for region in cal.regions.iter().filter(|r| r.count > 0) {
                let price = prices
                    .get(&region.circuit)
                    .unwrap_or_else(|| panic!("no measured price for {:?}", region.circuit));
                for d in 0..NUM_CENSUS_DIMS {
                    variable[d] += region.count as u64 * price[d];
                }
            }
            variable[TOTAL_ROW] = variable[..NUM_FAMILY_DIMS].iter().sum();
            let mut measured = [0; NUM_ROWS];
            measured[..NUM_CENSUS_DIMS].copy_from_slice(&cal.total);
            measured[TOTAL_ROW] = cal.total[..NUM_FAMILY_DIMS].iter().sum();
            core::array::from_fn(|d| {
                (
                    measured[d] as i64 - variable[d] as i64,
                    gate_budget(d, measured[d], proofs, spread[d]) as i64,
                )
            })
        })
        .collect();
    let interval = |d: usize| {
        rows.iter().fold((i64::MIN, i64::MAX), |(lo, hi), row| {
            let (intercept, budget) = row[d];
            (lo.max(intercept - budget), hi.min(intercept + budget))
        })
    };
    let mut c0: CensusVec = core::array::from_fn(|d| {
        let (lo, hi) = interval(d);
        assert!(lo <= hi && hi >= 0, "dim {d}: no nonnegative C0");
        (lo + (hi - lo) / 2).max(lo.max(0)) as u64
    });
    let sum: i64 = c0[..NUM_FAMILY_DIMS].iter().map(|v| *v as i64).sum();
    let (lo, hi) = interval(TOTAL_ROW);
    let mut remaining = sum.clamp(lo.max(0), hi) - sum;
    for (d, value) in c0[..NUM_FAMILY_DIMS].iter_mut().enumerate() {
        let (lo, hi) = interval(d);
        let current = *value as i64;
        let adjustment = remaining.clamp(lo.max(0) - current, hi - current);
        *value = (current + adjustment) as u64;
        remaining -= adjustment;
    }
    assert_eq!(remaining, 0, "family C0 sum must meet the total interval");
    PooledCensus {
        v: prices,
        c0,
        spread,
    }
}

pub fn render_census_tables(program: FsvProgram, pooled: &PooledCensus) -> String {
    let fmt_vec = |v: &CensusVec| {
        let inner: Vec<String> = v.iter().map(|x| x.to_string()).collect();
        format!("[{}]", inner.join(", "))
    };
    let mut out = String::new();
    let c0 = &pooled.c0;
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
    for circuit in compiled_circuits(program) {
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
    out
}
