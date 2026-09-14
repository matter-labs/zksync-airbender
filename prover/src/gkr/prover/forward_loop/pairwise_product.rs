use super::*;
use crate::allocation_pool::{AllocationPool, AllocationType, Buffer, ColumnLayout};
use crate::gkr::sumcheck::evaluation_kernels::{pairwise_product, BatchedGKRKernel};
use cs::gkr_compiler::SpecialMemoryContributionRelation;

pub fn forward_evaluate_pairwise_product<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::avx512::pairwise_product(
            inputs,
            output,
            gkr_storage,
            expected_output_layer,
            trace_len,
            pool,
            worker,
        );
    }
    forward_evaluate_pairwise_product_scalar(
        inputs,
        output,
        gkr_storage,
        expected_output_layer,
        trace_len,
        pool,
        worker,
    )
}

pub(crate) fn forward_evaluate_pairwise_product_scalar<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: [GKRAddress; 2],
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    // we just need to evaluate the corresponding kernel in the forward direction
    let kernel = pairwise_product::SameSizeProductGKRRelation { inputs, output };
    kernel.evaluate_forward_over_storage(
        gkr_storage,
        expected_output_layer,
        trace_len,
        pool,
        worker,
    );
}

pub fn forward_evaluate_base_layer_pairwise_product_without_caches<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: &[SpecialMemoryContributionRelation; 2],
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    expected_output_layer: usize,
    compiled_circuit: &GKRCircuitArtifact<F>,
    trace_len: usize,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len)
        && super::avx512::product_without_caches(
            inputs,
            output,
            gkr_storage,
            external_challenges,
            expected_output_layer,
            compiled_circuit,
            trace_len,
            pool,
            worker,
        )
    {
        return;
    }
    unsafe {
        let mut destination = pool.alloc_ext(trace_len, ColumnLayout::Contiguous);
        let ext_destination = vec![destination.as_mut()];
        let mut sources = Vec::with_capacity(compiled_circuit.memory_layout.total_width);
        for i in 0..compiled_circuit.memory_layout.total_width {
            let src = gkr_storage.get_base_layer_mem(i);
            sources.push(src);
        }
        let sources_ref = &sources[..];
        let [lhs, rhs] = inputs;

        apply_row_wise::<F, _>(
            vec![],
            ext_destination,
            trace_len,
            worker,
            |_, ext_dest, chunk_start, chunk_size| {
                assert_eq!(ext_dest.len(), 1);
                let mut ext_dest = ext_dest;
                let dest = ext_dest.pop().unwrap();
                for i in 0..chunk_size {
                    let absolute_row_idx = chunk_start + i;
                    let mut a = evaluate_memory_query(
                        lhs,
                        absolute_row_idx,
                        sources_ref,
                        external_challenges,
                    );
                    let b = evaluate_memory_query(
                        rhs,
                        absolute_row_idx,
                        sources_ref,
                        external_challenges,
                    );
                    a.mul_assign(&b);

                    dest.get_unchecked_mut(i).write(a);
                }
            },
        );
        assert_eq!(expected_output_layer, 1);
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            ExtensionFieldPoly::from_pooled(destination),
        );
    }
}
