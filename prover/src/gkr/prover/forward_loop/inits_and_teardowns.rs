use super::*;
use crate::allocation_pool::{AllocationPool, AllocationType};
use cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;

pub(crate) fn materialize_inits_and_teardowns_tuple_pair<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const WORD_BITS: u32,
    GB: crate::gkr::prover::gkr_backend::GKRBackend<F, E>,
>(
    gkr_backend: &GB,
    ts_and_value: &InitsOrTeardownsTimestampAndValue,
    address_high_bits: [u32; 2],
    gkr_storage: &GKRStorage<F, E>,
    trace_len: usize,
    external_challenges: &GKRExternalChallenges<F, E>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> AllocationType<E> {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if super::avx512::enabled::<F, E>(trace_len) {
        return super::avx512::inits_and_teardowns_pair::<F, E, WORD_BITS>(
            ts_and_value,
            address_high_bits,
            gkr_storage,
            trace_len,
            external_challenges,
            compiled_circuit,
            pool,
            worker,
        );
    }
    // Both sides as affine plans over the memory columns extended by the
    // inits/teardowns address columns; the backend evaluates their product.
    {
        let high_bits_offset = high_bits_offset_for_inits_and_teardowns::<WORD_BITS>(trace_len);
        let width = compiled_circuit.memory_layout.total_width;
        let mut columns: Vec<&[F]> = (0..width)
            .map(|i| gkr_storage.get_base_layer_mem(i))
            .collect();
        columns.push(gkr_storage.get_base_layer(GKRAddress::VirtualSetup(
            VirtualSetupPoly::InitsAndTeardownsLow,
        )));
        columns.push(gkr_storage.get_base_layer(GKRAddress::VirtualSetup(
            VirtualSetupPoly::InitsAndTeardownsHigh,
        )));
        let sides: [Option<([usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM], [usize; 2])>; 2] =
            match ts_and_value {
                InitsOrTeardownsTimestampAndValue::Init => [None, None],
                InitsOrTeardownsTimestampAndValue::Teardown {
                    lhs_timestamp,
                    lhs_value,
                    rhs_timestamp,
                    rhs_value,
                } => [
                    Some((*lhs_timestamp, *lhs_value)),
                    Some((*rhs_timestamp, *rhs_value)),
                ],
            };
        let plans: [_; 2] = core::array::from_fn(|k| {
            super::via_backend::compile_init_or_teardown(
                external_challenges,
                address_high_bits[k],
                high_bits_offset,
                sides[k],
                width,
                width + 1,
            )
        });
        super::via_backend::affine_plan_product(
            gkr_backend,
            &plans[0],
            &plans[1],
            &columns,
            trace_len,
            pool,
            worker,
        )
    }
}
