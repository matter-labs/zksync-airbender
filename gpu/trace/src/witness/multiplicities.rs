// Field instantiations supply only the counter representation, bound, allocation policy and symbols.
macro_rules! define_lookup_multiplicities {
    ($field:ty, $counter:ty, $mapping_len_bound:expr, $allocate_counters:path, $count:ident, $reduce:ident) => {
        era_cudart::cuda_kernel!(CountMultiplicities,
            $count(
                lookup_mapping: *mut u32,
                lookup_mapping_size: u32,
                counter_shards: *mut $counter,
                active_counts_len: u32,
                counter_replicas: u32,
            )
        );
        era_cudart::cuda_kernel!(ReduceConvertMultiplicities,
            $reduce(
                counter_shards: *const $counter,
                multiplicities: *mut $field,
                active_counts_len: u32,
                counter_replicas: u32,
            )
        );
        pub fn generate_lookup_multiplicities(
            lookup_mapping: &mut impl gpu_core::primitives::device_structures::DeviceMatrixMutImpl<u32>,
            multiplicities: &mut impl gpu_core::primitives::device_structures::DeviceMatrixMutImpl<$field>,
            active_counts_len: usize,
            context: &gpu_prover_context::ProverContext,
        ) -> era_cudart::result::CudaResult<()> {
            use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
            use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
            use gpu_ops::simple::set_to_zero;
            const COUNTER_REPLICAS: usize = 8;

            let stride = lookup_mapping.stride();
            assert!(stride.is_power_of_two());
            assert_eq!(stride, multiplicities.stride());
            let mapping_len = lookup_mapping.slice().len();
            let multiplicities_len = multiplicities.slice().len();
            let stream = context.get_exec_stream();
            set_to_zero(multiplicities.slice_mut(), stream)?;
            if mapping_len == 0 {
                return Ok(());
            }
            assert!(mapping_len < $mapping_len_bound);
            assert!(active_counts_len > 0);
            assert!(active_counts_len <= multiplicities_len);
            let counter_storage_len = active_counts_len * COUNTER_REPLICAS;
            assert!(counter_storage_len <= u32::MAX as usize);

            let mapping_len = mapping_len as u32;
            let active_counts_len = active_counts_len as u32;
            let counter_replicas = COUNTER_REPLICAS as u32;
            let multiplicities_ptr = multiplicities.as_mut_ptr();
            let mut counter_storage =
                $allocate_counters(counter_storage_len, multiplicities_len, context)?;
            let counter_shards = counter_storage
                .as_mut()
                .map_or(multiplicities_ptr.cast::<$counter>(), |storage| {
                    storage.as_mut_ptr()
                });
            let (grid_dim, block_dim) =
                get_grid_block_dims_for_threads_count(WARP_SIZE * 4, mapping_len);
            let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            let args = CountMultiplicitiesArguments::new(
                lookup_mapping.as_mut_ptr(),
                mapping_len,
                counter_shards,
                active_counts_len,
                counter_replicas,
            );
            CountMultiplicitiesFunction::default().launch(&config, &args)?;

            let (grid_dim, block_dim) =
                get_grid_block_dims_for_threads_count(WARP_SIZE * 4, active_counts_len);
            let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            let args = ReduceConvertMultiplicitiesArguments::new(
                counter_shards,
                multiplicities_ptr,
                active_counts_len,
                counter_replicas,
            );
            ReduceConvertMultiplicitiesFunction::default().launch(&config, &args)?;
            if counter_storage.is_none() {
                set_to_zero(
                    &mut multiplicities.slice_mut()[active_counts_len as usize..counter_storage_len],
                    stream,
                )?;
            }
            Ok(())
        }
    };
}
pub(crate) use define_lookup_multiplicities;
