use super::plan::{plan_unrolled_stream, RegionPlan, Section, StreamPlan};
use super::{load_calibration_proof, trace_verifier, Trace};
use full_statement_verifier::cost_model::CircuitId;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

pub const FIXTURES: &[(&str, FsvProgram)] = &[
    ("base", FsvProgram::UnrolledBaseLayer),
    ("rung0", FsvProgram::UnrolledRecursionLayer),
    ("rung1", FsvProgram::UnrolledRecursionLayer),
];

pub struct Calibration {
    pub total_cycles: u64,
    pub v: Vec<(CircuitId, u64)>,
    pub counts: Vec<(CircuitId, usize)>,
    pub spans: Vec<(CircuitId, Vec<u64>)>,
    pub unpriced: Vec<CircuitId>,
    pub s_riscv: u64,
    pub s_delegation: u64,
}

pub fn calibrate_fixture(name: &str, program: FsvProgram) -> Calibration {
    let (bin, text) = full_statement_verifier::host_utils::load_fsv_program(
        format!("{}/../tools/gkr_verifier", env!("CARGO_MANIFEST_DIR")),
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
    calibrate(&t, &plan)
}

pub fn calibrate(trace: &Trace, plan: &StreamPlan) -> Calibration {
    let cycle_at = |w: usize| trace.marks[w];
    let region_cycles = |r: &RegionPlan| cycle_at(r.end_word) - cycle_at(r.count_word);

    let spans_of = |r: &RegionPlan| -> Vec<u64> {
        r.proof_first_words
            .windows(2)
            .map(|w| cycle_at(w[1]) - cycle_at(w[0]))
            .collect()
    };
    let period_of = |r: &RegionPlan| -> Option<u64> {
        let spans = spans_of(r);
        if spans.is_empty() {
            None
        } else {
            let len = spans.len() as u64;
            Some((spans.iter().sum::<u64>() + len / 2) / len)
        }
    };

    let section_s = |section: Section| -> u64 {
        plan.regions
            .iter()
            .filter(|r| r.section == section && !r.closes_at_epilogue)
            .find_map(|r| {
                period_of(r).map(|v| {
                    let priced = r.proof_first_words.len() as u64 * v;
                    region_cycles(r).checked_sub(priced).unwrap_or_else(|| {
                        panic!(
                            "{:?}: region_cycles {} < n*v {}, so S_{:?} would be negative",
                            r.circuit,
                            region_cycles(r),
                            priced,
                            section
                        )
                    })
                })
            })
            .unwrap_or_else(|| {
                panic!(
                    "calibration precondition violated: the {section:?} section has no \
                     interior circuit type with n >= 2, so its per-type overhead cannot be \
                     measured. Use a fixture with more proofs."
                )
            })
    };

    let s_riscv = section_s(Section::Riscv);
    let s_delegation = section_s(Section::Delegation);

    let mut v = Vec::new();
    let mut counts = Vec::new();
    let mut spans = Vec::new();
    let mut unpriced = Vec::new();

    for r in &plan.regions {
        let n = r.proof_first_words.len();
        counts.push((r.circuit, n));
        spans.push((r.circuit, spans_of(r)));

        if n == 0 {
            unpriced.push(r.circuit);
            continue;
        }
        let cost = match period_of(r) {
            Some(period) => period,
            None if !r.closes_at_epilogue => {
                let s = match r.section {
                    Section::Riscv => s_riscv,
                    Section::Delegation => s_delegation,
                };
                region_cycles(r).checked_sub(s).unwrap_or_else(|| {
                    panic!(
                        "{:?}: region_cycles {} < S_{:?} {}",
                        r.circuit,
                        region_cycles(r),
                        r.section,
                        s
                    )
                })
            }
            None => panic!(
                "{:?} is a singleton in the epilogue-tail region; its span includes the \
                 transcript finalization and PoW transition, so it cannot be priced from \
                 this fixture. Use a fixture where it has >= 2 proofs.",
                r.circuit
            ),
        };
        v.push((r.circuit, cost));
    }

    Calibration {
        total_cycles: trace.total_cycles,
        v,
        counts,
        spans,
        unpriced,
        s_riscv,
        s_delegation,
    }
}
