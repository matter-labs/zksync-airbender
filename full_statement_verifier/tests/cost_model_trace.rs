#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg(all(feature = "host_utils", feature = "verifiers"))]

mod trace;

use trace::fsv_dir;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

fn load_base_layer() -> (Vec<u32>, Vec<u32>) {
    full_statement_verifier::host_utils::load_fsv_program(
        fsv_dir(),
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
    )
}

#[test]
#[ignore = "needs a real base proof; see Task 6"]
fn marks_are_monotonic_and_one_per_stream_word() {
    let (bin, text) = load_base_layer();
    let (setups, proof) = trace::load_calibration_proof("base");
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
    let expected_reads = stream.len();

    let t = trace::trace_verifier(&bin, &text, stream);

    assert_eq!(
        t.marks.len(),
        expected_reads,
        "one ND read per stream word: read index is the stream word index"
    );
    assert!(
        t.marks.windows(2).all(|w| w[0] <= w[1]),
        "marks must be non-decreasing"
    );
    assert!(t.marks.last().copied().unwrap_or(0) <= t.total_cycles);
}

#[test]
#[ignore = "needs a real base proof; see Task 6"]
fn total_cycles_matches_the_uninstrumented_measurement() {
    let (bin, text) = load_base_layer();
    let (setups, proof) = trace::load_calibration_proof("base");
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);

    let instrumented = trace::trace_verifier(&bin, &text, stream.clone()).total_cycles;
    let plain = trace::measure_verifier_cycles(&bin, &text, stream);

    assert_eq!(
        instrumented, plain,
        "instrumentation must not perturb the guest's cycle count"
    );
}

#[test]
#[ignore = "needs real proofs; see Task 6"]
fn stream_plan_matches_the_actual_stream() {
    for (fixture, program) in trace::calibrate::FIXTURES {
        let (setups, proof) = trace::load_calibration_proof(fixture);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
        let plan = trace::plan::plan_unrolled_stream(&setups, &proof, *program);

        assert_eq!(
            plan.total_words,
            stream.len(),
            "{fixture}: planned length must match the stream"
        );

        for region in &plan.regions {
            let n = region.proof_first_words.len() as u32;
            assert_eq!(
                stream[region.count_word], n,
                "{fixture}: planned count word for {:?} must hold its proof count",
                region.circuit
            );
        }
        assert_eq!(stream[plan.inits_count_word], 1);
        assert_eq!(
            plan.inits_first_word,
            plan.inits_count_word + 1,
            "{fixture}: the inits/teardowns proof must start right after its count word"
        );
        assert_eq!(
            plan.prefix_words, plan.regions[0].count_word,
            "{fixture}: the first RISC-V count word must sit at the end of the prefix"
        );

        let riscv: Vec<_> = plan
            .regions
            .iter()
            .filter(|r| r.section == trace::plan::Section::Riscv)
            .collect();
        assert_eq!(
            riscv.len(),
            full_statement_verifier::cost_model::riscv_order(*program).len(),
            "{fixture}: one region per compiled RISC-V family"
        );
        assert_eq!(
            riscv.last().unwrap().end_word,
            plan.inits_count_word,
            "{fixture}: the last RISC-V region must close at the inits/teardowns count word, \
             not at the first delegation region"
        );
        let deleg: Vec<_> = plan
            .regions
            .iter()
            .filter(|r| r.section == trace::plan::Section::Delegation)
            .collect();
        assert_eq!(deleg.last().unwrap().end_word, plan.pow_word);
        assert!(deleg.last().unwrap().closes_at_epilogue);
        assert!(riscv.iter().all(|r| !r.closes_at_epilogue));

        let expected_pow_low = proof.pow_challenge as u32;
        assert_eq!(
            stream[plan.pow_word], expected_pow_low,
            "{fixture}: final sentinel must land on the first PoW word"
        );
    }
}

#[test]
#[ignore = "needs real proofs; see Task 6"]
fn per_proof_spans_agree_within_a_circuit() {
    for (fixture, program) in trace::calibrate::FIXTURES {
        let c = trace::calibrate::calibrate_fixture(fixture, *program);
        for (circuit, spans) in &c.spans {
            if spans.len() < 2 {
                continue;
            }
            let lo = *spans.iter().min().unwrap();
            let hi = *spans.iter().max().unwrap();
            assert!(
                hi - lo <= hi / 200,
                "{fixture}/{circuit:?}: per-proof spans vary more than 0.5% \
                 (min {lo}, max {hi}) — the affine model does not hold for this circuit"
            );
        }
    }
}

#[test]
#[ignore = "needs real proofs; see Task 6"]
fn proof_counts_matches_the_planned_regions() {
    use full_statement_verifier::cost_model::proof_counts;
    for (fixture, program) in trace::calibrate::FIXTURES {
        let (setups, proof) = trace::load_calibration_proof(fixture);
        let plan = trace::plan::plan_unrolled_stream(&setups, &proof, *program);
        let mut from_api: Vec<_> = proof_counts(&proof)
            .into_iter()
            .filter(|(_, n)| *n > 0)
            .collect();
        let mut from_plan: Vec<_> = plan
            .regions
            .iter()
            .map(|r| (r.circuit, r.proof_first_words.len()))
            .filter(|(_, n)| *n > 0)
            .collect();
        from_api.sort();
        from_plan.sort();
        assert_eq!(
            from_api, from_plan,
            "{fixture}: proof_counts disagrees with the stream plan"
        );
    }
}

#[test]
#[ignore = "needs real proofs; see Task 6"]
fn implied_per_type_overhead_agrees_within_a_section() {
    use trace::plan::Section;
    for (fixture, program) in trace::calibrate::FIXTURES {
        let (t, plan) = trace::calibrate::trace_fixture(fixture, *program);
        for section in [Section::Riscv, Section::Delegation] {
            let observed = trace::calibrate::implied_section_s(&t, &plan, section);
            let lo = observed.iter().map(|(_, s)| *s).min().unwrap();
            let hi = observed.iter().map(|(_, s)| *s).max().unwrap();
            assert!(
                hi - lo <= hi / 200,
                "{fixture}/{section:?}: the implied per-type overhead S varies more than 0.5% \
                 across regions {observed:?} — singletons priced as region_cycles - S are \
                 mispriced by the spread"
            );
        }
    }
}

#[test]
#[ignore = "needs real proofs; see Task 6"]
fn emit_cost_tables() {
    let cals: Vec<_> = trace::calibrate::FIXTURES
        .iter()
        .map(|(name, program)| {
            (
                *name,
                *program,
                trace::calibrate::calibrate_fixture(name, *program),
            )
        })
        .collect();
    let pooled = trace::calibrate::pool(&cals);

    assert_eq!(
        pooled.unpriced,
        vec![full_statement_verifier::cost_model::CircuitId::Delegation(
            common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER
        )],
        "only blake2_g_function may remain unpriced; anything else means a fixture gap"
    );

    println!("{}", trace::calibrate::render_tables(&pooled));
}

#[test]
#[ignore = "needs real proofs; see Task 6"]
fn estimate_matches_measurement_on_every_fixture() {
    use full_statement_verifier::cost_model::estimate_verifier_cycles;

    for (name, program) in trace::calibrate::FIXTURES {
        let (bin, text) = full_statement_verifier::host_utils::load_fsv_program(
            fsv_dir(),
            *program,
            BlakeMode::Compression,
        );
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);

        let measured = trace::measure_verifier_cycles(&bin, &text, stream);
        let est = estimate_verifier_cycles(&proof, *program, BlakeMode::Compression).unwrap();

        let err = (est as i64 - measured as i64).unsigned_abs();
        let budget = measured / 2000;
        assert!(
            err <= budget,
            "{name}: estimate {est} vs measured {measured} exceeds the 0.05% budget \
             ({err} > {budget})"
        );
    }
}
