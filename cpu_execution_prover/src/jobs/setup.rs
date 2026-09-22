//! Setup initialization: commit a circuit's setup columns once.
//!
//! Runs for every registered circuit, including a family with no execution
//! instances: its setup cap still enters the verifier's parameters.

use super::CpuJobs;
use crate::precomputations::CpuCircuitPrecomputations;
use execution_prover::messages::{SetupInitializationRequest, SetupInitializationResult};
use execution_prover::prover_config;
use worker::Worker;

pub(crate) fn run(
    jobs: &CpuJobs,
    request: SetupInitializationRequest<CpuCircuitPrecomputations>,
    worker: &Worker,
) -> SetupInitializationResult {
    let SetupInitializationRequest {
        batch_id,
        circuit_type,
        sequence_id,
        precomputations,
        security_level,
    } = request;
    // The same geometry the memory and proof jobs use: a setup committed under
    // one configuration cannot be verified against another.
    let config = prover_config(circuit_type, security_level);
    let twiddles = jobs.twiddles(precomputations.trace_len, worker);
    precomputations.initialize_setup(&config, &*twiddles, worker);
    SetupInitializationResult {
        batch_id,
        circuit_type,
        sequence_id,
    }
}
