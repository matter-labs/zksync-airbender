use crate::allocation_pool::{AllocationPool, AllocationType, Buffer, ColumnLayout};
use crate::gkr::sumcheck::evaluation_kernels::{lookup_pair, BatchedGKRKernel};

use super::*;

pub fn forward_evaluate_lookup_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [[GKRAddress; 2]; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::avx512::lookup_pair(
            inputs,
            outputs,
            gkr_storage,
            expected_output_layer,
            trace_len,
            pool,
            worker,
        );
    }
    forward_evaluate_lookup_pair_scalar(
        inputs,
        outputs,
        gkr_storage,
        expected_output_layer,
        trace_len,
        pool,
        worker,
    )
}

pub(crate) fn forward_evaluate_lookup_pair_scalar<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [[GKRAddress; 2]; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    let kernel = lookup_pair::LookupPairGKRRelation { inputs, outputs };
    kernel.evaluate_forward_over_storage(
        gkr_storage,
        expected_output_layer,
        trace_len,
        pool,
        worker,
    );
}
