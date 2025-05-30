#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]
#![feature(let_chains)]
#![feature(adt_const_params)]

use itertools::Itertools;
use execution_utils::get_padded_binary;
use gpu_prover::circuit_type::MainCircuitType;
use gpu_prover::execution::prover::{ExecutableBinary, ExecutionProver};
use log::{info, LevelFilter};
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use std::hash::{DefaultHasher, Hash, Hasher};
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
    let mut previous_hashes = None;
    loop {
        let result = prover.commit_memory(0, &hashed_fibonacci, 64, non_determinism.clone());
        let hashes = result
            .1
            .into_iter()
            .map(|x| {
                let mut hasher = DefaultHasher::new();
                x.hash(&mut hasher);
                hasher.finish()
            })
            .collect_vec();
        if let Some(previous) = &previous_hashes {
            assert_eq!(previous, &hashes);
        } else {
            previous_hashes = Some(hashes);
        }
    }
}
