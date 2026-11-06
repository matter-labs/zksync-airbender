//! Regenerate the small full-statement verifier proof used by Miri CI.
#![feature(allocator_api)]
#[path = "../../full_statement_verifier/tests/common/hashed_fibonacci.rs"]
mod fixture;

use prover::definitions::{SecurityLevel, SoundnessMode};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

fn main() {
    let mut args = std::env::args_os().skip(1);
    let out = std::path::absolute(
        args.next()
            .expect("usage: hashed_fibonacci_fixture OUTPUT_DIR"),
    )
    .unwrap();
    assert!(
        args.next().is_none(),
        "usage: hashed_fibonacci_fixture OUTPUT_DIR"
    );
    // Keep paths used by the existing producer consistent with its native tests.
    std::env::set_current_dir(env!("CARGO_MANIFEST_DIR")).unwrap();
    let (binary, text) = fixture::program();
    let worker = prover::worker::Worker::new_with_num_threads(8);
    let started = std::time::Instant::now();
    eprintln!("PHASE prove-begin");
    let (proof, setups) = program_prover::unrolled::prove_unrolled_execution_with_replayer_in_mode::<
        riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly,
        std::alloc::Global,
        _,
        _,
    >(
        1 << 16,
        &binary,
        &text,
        true,
        QuasiUARTSource::new_with_reads(fixture::READS.to_vec()),
        1 << 30,
        &worker,
        SecurityLevel::Sec100,
        SoundnessMode::PessimisticConjecture,
        verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
        &prover::gkr::prover::DefaultBabyBearBackend::default(),
        &prover::gkr::prover::DefaultBabyBearGKRBackend::default(),
    );
    eprintln!(
        "PHASE prove-end ({:.3} seconds)",
        started.elapsed().as_secs_f64()
    );
    fixture::write_fixture(proof, setups, &out);
}
