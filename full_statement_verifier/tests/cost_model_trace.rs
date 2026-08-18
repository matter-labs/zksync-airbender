#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg(all(feature = "host_utils", feature = "verifiers"))]

mod trace;

use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

fn fsv_dir() -> String {
    format!("{}/../tools/gkr_verifier", env!("CARGO_MANIFEST_DIR"))
}

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
#[ignore = "needs a real base proof; see Task 6"]
fn stream_plan_matches_the_actual_stream() {
    use verifier_common::fsv_binaries::FsvProgram;
    let (setups, proof) = trace::load_calibration_proof("base");
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
    let plan = trace::plan::plan_unrolled_stream(&setups, &proof, FsvProgram::UnrolledBaseLayer);

    assert_eq!(
        plan.total_words,
        stream.len(),
        "planned length must match the stream"
    );

    for region in &plan.regions {
        let n = region.proof_first_words.len() as u32;
        assert_eq!(
            stream[region.count_word], n,
            "planned count word for {:?} must hold its proof count",
            region.circuit
        );
    }
    assert_eq!(stream[plan.inits_count_word], 1);

    let riscv: Vec<_> = plan
        .regions
        .iter()
        .filter(|r| r.section == trace::plan::Section::Riscv)
        .collect();
    assert_eq!(
        riscv.last().unwrap().end_word,
        plan.inits_count_word,
        "the last RISC-V region must close at the inits/teardowns count word, \
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
        "final sentinel must land on the first PoW word"
    );
}
