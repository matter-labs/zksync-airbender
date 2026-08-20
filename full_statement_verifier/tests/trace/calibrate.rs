use super::plan::{plan_unrolled_stream, RegionPlan, Section, StreamPlan};
use super::{fsv_dir, load_calibration_proof, trace_verifier, Trace};
use full_statement_verifier::cost_model::census::{CensusVec, NUM_CENSUS_DIMS};
use full_statement_verifier::cost_model::{compiled_circuits, CircuitId};
use std::collections::BTreeMap;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

pub struct Fixture {
    pub name: &'static str,
    pub program: FsvProgram,
    /// Whether coefficients may be derived from it: `calibrate` fits each
    /// section's `S` from one non-epilogue region with `n >= 2` in that section,
    /// so a fixture without one anywhere can only be checked end to end. Every
    /// other circuit type may be a singleton, priced as `region_cycles - S`.
    pub calibrated: bool,
}

pub const ALL_FIXTURES: &[Fixture] = &[
    Fixture {
        name: "base",
        program: FsvProgram::UnrolledBaseLayer,
        calibrated: true,
    },
    Fixture {
        name: "base_alt",
        program: FsvProgram::UnrolledBaseLayer,
        calibrated: true,
    },
    Fixture {
        name: "recursion0",
        program: FsvProgram::UnrolledRecursionLayer,
        calibrated: true,
    },
    Fixture {
        name: "recursion1",
        program: FsvProgram::UnrolledRecursionLayer,
        calibrated: false,
    },
];

pub fn calibration_fixtures() -> impl Iterator<Item = &'static Fixture> {
    ALL_FIXTURES.iter().filter(|f| f.calibrated)
}

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

/// The census fit, run independently per dimension (per-family cycles,
/// delegation calls).
pub struct CensusCalibration {
    pub total: CensusVec,
    pub v: Vec<(CircuitId, CensusVec)>,
    pub counts: Vec<(CircuitId, usize)>,
    pub spans: Vec<(CircuitId, Vec<CensusVec>)>,
}

fn region_census(trace: &Trace, r: &RegionPlan, d: usize) -> u64 {
    trace.census_marks[r.end_word][d] - trace.census_marks[r.count_word][d]
}

fn census_spans_of(trace: &Trace, r: &RegionPlan, d: usize) -> Vec<u64> {
    r.proof_first_words
        .windows(2)
        .map(|w| trace.census_marks[w[1]][d] - trace.census_marks[w[0]][d])
        .collect()
}

fn census_period_of(trace: &Trace, r: &RegionPlan, d: usize) -> Option<u64> {
    let spans = census_spans_of(trace, r, d);
    if spans.is_empty() {
        None
    } else {
        let len = spans.len() as u64;
        Some((spans.iter().sum::<u64>() + len / 2) / len)
    }
}

pub fn calibrate_census_fixture(name: &str, program: FsvProgram) -> CensusCalibration {
    let (t, plan) = trace_fixture(name, program);
    calibrate_census(&t, &plan)
}

pub fn calibrate_census(trace: &Trace, plan: &StreamPlan) -> CensusCalibration {
    let section_s = |section: Section, d: usize| -> i64 {
        plan.regions
            .iter()
            .filter(|r| r.section == section && !r.closes_at_epilogue)
            .find_map(|r| {
                census_period_of(trace, r, d).map(|v| {
                    let priced = r.proof_first_words.len() as u64 * v;
                    region_census(trace, r, d) as i64 - priced as i64
                })
            })
            .unwrap_or_else(|| {
                panic!(
                    "calibration precondition violated: the {section:?} section has no \
                     interior circuit type with n >= 2 (census dim {d})"
                )
            })
    };

    let s_riscv: [i64; NUM_CENSUS_DIMS] = core::array::from_fn(|d| section_s(Section::Riscv, d));
    let s_delegation: [i64; NUM_CENSUS_DIMS] =
        core::array::from_fn(|d| section_s(Section::Delegation, d));

    let mut v = Vec::new();
    let mut counts = Vec::new();
    let mut spans = Vec::new();

    for r in &plan.regions {
        let n = r.proof_first_words.len();
        counts.push((r.circuit, n));
        let per_dim: Vec<Vec<u64>> = (0..NUM_CENSUS_DIMS)
            .map(|d| census_spans_of(trace, r, d))
            .collect();
        let raw_spans: Vec<CensusVec> = (0..per_dim[0].len())
            .map(|i| core::array::from_fn(|d| per_dim[d][i]))
            .collect();
        spans.push((r.circuit, raw_spans));

        if n == 0 {
            continue;
        }
        let cost: CensusVec = core::array::from_fn(|d| match census_period_of(trace, r, d) {
            Some(period) => period,
            None if !r.closes_at_epilogue => {
                let s = match r.section {
                    Section::Riscv => s_riscv[d],
                    Section::Delegation => s_delegation[d],
                };
                let count = region_census(trace, r, d);
                u64::try_from(count as i64 - s).unwrap_or_else(|_| {
                    panic!(
                        "{:?} dim {d}: region census {} < S_{:?} {}",
                        r.circuit, count, r.section, s
                    )
                })
            }
            None => panic!(
                "{:?} is a singleton in the epilogue-tail region; use a fixture where it \
                 has >= 2 proofs (census dim {d})",
                r.circuit
            ),
        });
        v.push((r.circuit, cost));
    }

    CensusCalibration {
        total: trace.total_census,
        v,
        counts,
        spans,
    }
}

pub struct PooledCensus {
    pub v: BTreeMap<CircuitId, CensusVec>,
    pub c0: Vec<(FsvProgram, CensusVec)>,
}

/// Sanity bounds on the fit's premises (the acceptance test is the binding
/// gate). 1/64 slack: data-dependent jitter shifts cycles between families
/// while the total holds 0.05%. The floor spares tiny counts exactness.
const CENSUS_REL_DIV: u64 = 64;
const CENSUS_ABS_FLOOR: u64 = 8;

pub fn pool_census(cals: &[(&str, FsvProgram, CensusCalibration)]) -> PooledCensus {
    let mut observations: BTreeMap<CircuitId, Vec<CensusVec>> = BTreeMap::new();
    for (_, _, c) in cals {
        for (circuit, cost) in &c.v {
            observations.entry(*circuit).or_default().push(*cost);
        }
    }

    let mut v = BTreeMap::new();
    for (circuit, obs) in &observations {
        let pooled: CensusVec = core::array::from_fn(|d| {
            let lo = obs.iter().map(|c| c[d]).min().unwrap();
            let hi = obs.iter().map(|c| c[d]).max().unwrap();
            assert!(
                hi - lo <= (hi / CENSUS_REL_DIV).max(CENSUS_ABS_FLOOR),
                "{circuit:?} census dim {d} differs by more than the pooling bound across \
                 fixtures (min {lo}, max {hi})"
            );
            obs.iter().map(|c| c[d]).sum::<u64>() / obs.len() as u64
        });
        v.insert(*circuit, pooled);
    }

    let mut fits: Vec<(FsvProgram, CensusVec, CensusVec)> = Vec::new();
    for (name, program, c) in cals {
        let fitted: CensusVec = core::array::from_fn(|d| {
            let priced: u64 = c
                .counts
                .iter()
                .map(|(circuit, n)| {
                    if *n == 0 {
                        return 0;
                    }
                    *n as u64
                        * v.get(circuit).unwrap_or_else(|| {
                            panic!("{name}: {circuit:?} has {n} proofs but no pooled census")
                        })[d]
                })
                .sum();
            c.total[d].checked_sub(priced).unwrap_or_else(|| {
                panic!(
                    "{name}: census dim {d} total {} < priced {priced}, so C0 for \
                     {program:?} would be negative",
                    c.total[d]
                )
            })
        });
        if let Some((_, existing, existing_total)) = fits.iter().find(|(p, _, _)| p == program) {
            for d in 0..NUM_CENSUS_DIMS {
                let spread = fitted[d].max(existing[d]) - fitted[d].min(existing[d]);
                let scale = c.total[d].min(existing_total[d]);
                let budget = (scale / CENSUS_REL_DIV).max(CENSUS_ABS_FLOOR);
                assert!(
                    spread <= budget,
                    "{name}: census C0 dim {d} for {program:?} is {} here but {} from \
                     another fixture — spread {spread} over budget {budget}",
                    fitted[d],
                    existing[d]
                );
            }
        } else {
            fits.push((*program, fitted, c.total));
        }
    }
    let c0 = fits.into_iter().map(|(p, fitted, _)| (p, fitted)).collect();

    PooledCensus { v, c0 }
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
            v: &[
",
            fmt_vec(c0)
        ));
        for circuit in compiled_circuits(*program) {
            if let Some(cost) = pooled.v.get(&circuit) {
                let id = match circuit {
                    CircuitId::Riscv(k) => format!("CircuitId::Riscv({k})"),
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
