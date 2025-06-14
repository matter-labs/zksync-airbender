#![feature(allocator_api)]
#![feature(vec_push_within_capacity)]
#![feature(new_zeroed_alloc)]
#![feature(iter_array_chunks)]
#![feature(let_chains)]
#![feature(adt_const_params)]

pub mod cpu_worker;
pub mod gpu_worker;
pub mod logger;
pub mod messages;
// mod old_tracer;
pub mod batch_prover;
pub mod gpu_manager;
pub mod precomputations;
pub mod tracer;

use crate::batch_prover::GpuBatchProver;
use execution_utils::get_padded_binary;
use gpu_prover::circuit_type::MainCircuitType;
use log::{info, LevelFilter};
use prover::risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use std::io::Read;
use std::sync::Arc;

fn main() {
    env_logger::builder()
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .filter_level(LevelFilter::Info)
        .init();
    rayon::scope(|scope| {
        let mut prover = GpuBatchProver::new(12, 30, 2, scope);
        let mut binary = vec![];
        std::fs::File::open("examples/hashed_fibonacci/app.bin")
            .unwrap()
            .read_to_end(&mut binary)
            .unwrap();
        let bytecode = get_padded_binary(&binary);
        info!("loaded binary");
        let app_name = "hashed_fibonacci";
        prover.add_binary(app_name, MainCircuitType::RiscVCycles, bytecode);
        let prover = Arc::new(prover);
        let non_determinism = QuasiUARTSource::new_with_reads(vec![0, 1 << 17]);
        let pc = prover.clone();
        let ndc = non_determinism.clone();
        scope.spawn(move |_| {
            let result = pc.commit_memory(0, &app_name, 64, ndc);
            info!("Result: {:?}", result.0);
        });
        let pc = prover.clone();
        let ndc = non_determinism.clone();
        // let non_determinism = QuasiUARTSource::new_with_reads(vec![1 << 24, 0]);
        scope.spawn(move |_| {
            let result = pc.commit_memory(1, &app_name, 64, ndc);
            info!("Result: {:?}", result.0);
        });
        // prover.get_results(false, 0, "fibonacci", 64, non_determinism, None);
    });
}
