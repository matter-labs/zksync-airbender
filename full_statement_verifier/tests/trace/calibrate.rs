use super::plan::{plan_unrolled_stream, RegionPlan, Section, StreamPlan};
use super::{fsv_dir, load_calibration_proof, trace_verifier, Trace};
use full_statement_verifier::cost_model::{compiled_circuits, CircuitId};
use std::collections::BTreeMap;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

/// Fixtures that coefficients are derived from. Every circuit type they carry
/// must appear at least twice somewhere, or its per-type overhead is unmeasurable.
pub const CALIBRATION_FIXTURES: &[(&str, FsvProgram)] = &[
    ("base", FsvProgram::UnrolledBaseLayer),
    ("base_alt", FsvProgram::UnrolledBaseLayer),
    ("rung0", FsvProgram::UnrolledRecursionLayer),
];

/// Every fixture, including the steady rung, which carries one proof of each
/// type and so can only be checked end to end.
pub const ALL_FIXTURES: &[(&str, FsvProgram)] = &[
    ("base", FsvProgram::UnrolledBaseLayer),
    ("base_alt", FsvProgram::UnrolledBaseLayer),
    ("rung0", FsvProgram::UnrolledRecursionLayer),
    ("rung1", FsvProgram::UnrolledRecursionLayer),
];

pub struct Calibration {
    pub total_cycles: u64,
    pub v: Vec<(CircuitId, u64)>,
    pub counts: Vec<(CircuitId, usize)>,
    pub spans: Vec<(CircuitId, Vec<u64>)>,
    pub unpriced: Vec<CircuitId>,
    pub s_riscv: i64,
    pub s_delegation: i64,
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

pub fn calibrate_fixture(name: &str, program: FsvProgram) -> Calibration {
    let (t, plan) = trace_fixture(name, program);
    calibrate(&t, &plan)
}

fn region_cycles(trace: &Trace, r: &RegionPlan) -> u64 {
    trace.marks[r.end_word] - trace.marks[r.count_word]
}

fn spans_of(trace: &Trace, r: &RegionPlan) -> Vec<u64> {
    r.proof_first_words
        .windows(2)
        .map(|w| trace.marks[w[1]] - trace.marks[w[0]])
        .collect()
}

fn period_of(trace: &Trace, r: &RegionPlan) -> Option<u64> {
    let spans = spans_of(trace, r);
    if spans.is_empty() {
        None
    } else {
        let len = spans.len() as u64;
        Some((spans.iter().sum::<u64>() + len / 2) / len)
    }
}

/// `region_cycles - n*v` per region: the per-type overhead each one implies.
pub fn implied_section_s(
    trace: &Trace,
    plan: &StreamPlan,
    section: Section,
) -> Vec<(CircuitId, i64)> {
    plan.regions
        .iter()
        .filter(|r| r.section == section && !r.closes_at_epilogue)
        .filter_map(|r| {
            period_of(trace, r).map(|v| {
                let priced = r.proof_first_words.len() as u64 * v;
                (r.circuit, region_cycles(trace, r) as i64 - priced as i64)
            })
        })
        .collect()
}

pub fn calibrate(trace: &Trace, plan: &StreamPlan) -> Calibration {
    let section_s = |section: Section| -> i64 {
        implied_section_s(trace, plan, section)
            .first()
            .map(|(_, s)| *s)
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
        spans.push((r.circuit, spans_of(trace, r)));

        if n == 0 {
            unpriced.push(r.circuit);
            continue;
        }
        let cost = match period_of(trace, r) {
            Some(period) => period,
            None if !r.closes_at_epilogue => {
                let s = match r.section {
                    Section::Riscv => s_riscv,
                    Section::Delegation => s_delegation,
                };
                let cycles = region_cycles(trace, r);
                u64::try_from(cycles as i64 - s).unwrap_or_else(|_| {
                    panic!(
                        "{:?}: region_cycles {} < S_{:?} {}",
                        r.circuit, cycles, r.section, s
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

pub struct Pooled {
    pub v: BTreeMap<CircuitId, u64>,
    pub c0: Vec<(FsvProgram, u64)>,
    pub unpriced: Vec<CircuitId>,
}

pub fn pool(cals: &[(&str, FsvProgram, Calibration)]) -> Pooled {
    let mut observations: BTreeMap<CircuitId, Vec<(String, u64)>> = BTreeMap::new();
    for (name, _, c) in cals {
        for (circuit, cost) in &c.v {
            observations
                .entry(*circuit)
                .or_default()
                .push(((*name).to_string(), *cost));
        }
    }

    let mut v = BTreeMap::new();
    for (circuit, obs) in &observations {
        let lo = obs.iter().map(|(_, c)| *c).min().unwrap();
        let hi = obs.iter().map(|(_, c)| *c).max().unwrap();
        assert!(
            hi - lo <= hi / 200,
            "{circuit:?} costs differ by more than 0.5% across fixtures {obs:?} — \
             the same compiled circuit is not costing the same in both binaries, \
             which the design assumes"
        );
        v.insert(
            *circuit,
            obs.iter().map(|(_, c)| *c).sum::<u64>() / obs.len() as u64,
        );
    }

    let mut fits: Vec<(FsvProgram, u64, u64)> = Vec::new();
    for (name, program, c) in cals {
        let priced: u64 = c
            .counts
            .iter()
            .map(|(circuit, n)| *n as u64 * v.get(circuit).copied().unwrap_or(0))
            .sum();
        let fitted = c.total_cycles - priced;
        if let Some((_, existing, existing_total)) = fits.iter().find(|(p, _, _)| p == program) {
            let spread = fitted.max(*existing) - fitted.min(*existing);
            let scale = c.total_cycles.min(*existing_total);
            let budget = scale / 2000;
            assert!(
                spread <= budget,
                "{name}: C0 for {program:?} is {fitted} here but {existing} from another \
                 fixture — the presence-mask residual is {spread} cycles, {:.4}% of the \
                 {scale}-cycle estimate it perturbs, over the 0.05% budget ({budget}). C0 is \
                 not composition-independent, which breaks the model (spec section 2); the \
                 tag term needs an explicit per-section coefficient (spec section 10)",
                spread as f64 * 100.0 / scale as f64
            );
        } else {
            fits.push((*program, fitted, c.total_cycles));
        }
    }
    let c0 = fits.into_iter().map(|(p, fitted, _)| (p, fitted)).collect();

    let mut unpriced = Vec::new();
    for (_, program, _) in cals {
        for circuit in compiled_circuits(*program) {
            if !v.contains_key(&circuit) && !unpriced.contains(&circuit) {
                unpriced.push(circuit);
            }
        }
    }

    Pooled { v, c0, unpriced }
}

pub fn render_tables(pooled: &Pooled) -> String {
    let mut out = String::new();
    for (program, c0) in &pooled.c0 {
        out.push_str(&format!(
            "    (FsvProgram::{program:?}, BlakeMode::Compression, CostTable {{\n        c0: {c0},\n        v: &[\n"
        ));
        for circuit in compiled_circuits(*program) {
            if let Some(cost) = pooled.v.get(&circuit) {
                let id = match circuit {
                    CircuitId::Riscv(k) => format!("CircuitId::Riscv({k})"),
                    CircuitId::Delegation(k) => format!("CircuitId::Delegation({k})"),
                };
                out.push_str(&format!("            ({id}, {cost}),\n"));
            }
        }
        out.push_str("        ],\n    }),\n");
    }
    if !pooled.unpriced.is_empty() {
        out.push_str(&format!("    // unpriced: {:?}\n", pooled.unpriced));
    }
    out
}
