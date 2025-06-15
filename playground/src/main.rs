#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]
#![feature(let_chains)]
#![feature(adt_const_params)]

use execution_utils::get_padded_binary;
use gpu_prover::circuit_type::MainCircuitType;
use gpu_prover::execution::prover::{ExecutableBinary, ExecutionProver};
use log::{info, LevelFilter};
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use std::io::Read;

fn main() {
    env_logger::builder()
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .filter_level(LevelFilter::Info)
        .init();
    let path = "examples/hashed_fibonacci/app.bin";
    let mut binary = vec![];
    std::fs::File::open(path)
        .unwrap()
        .read_to_end(&mut binary)
        .unwrap();
    let bytecode = get_padded_binary(&binary);
    info!("loaded binary \"{path}\"");
    let hashed_fibonacci = "hashed_fibonacci";
    let hashed_fibonacci_binary = ExecutableBinary {
        key: hashed_fibonacci,
        circuit_type: MainCircuitType::RiscVCycles,
        bytecode,
    };
    let binaries = vec![hashed_fibonacci_binary];
    let prover = ExecutionProver::new(1, binaries);
    let non_determinism = QuasiUARTSource::new_with_reads(vec![1 << 24, 0]);
    // let prover = Arc::new(prover);
    // let pc = prover.clone();
    // let ndc = non_determinism.clone();
    // scope.spawn(move |_| {
    //     let result = pc.commit_memory(0, &app_name, 64, ndc);
    //     info!("Result: {:?}", result.0);
    // });
    // let pc = prover.clone();
    // let ndc = non_determinism.clone();
    // // let non_determinism = QuasiUARTSource::new_with_reads(vec![1 << 24, 0]);
    // scope.spawn(move |_| {
    //     let result = pc.commit_memory(1, &app_name, 64, ndc);
    //     info!("Result: {:?}", result.0);
    // });
    let result = prover.commit_memory(0, &hashed_fibonacci, 64, non_determinism);
    info!("Result: {:#?}", result.0);
}
