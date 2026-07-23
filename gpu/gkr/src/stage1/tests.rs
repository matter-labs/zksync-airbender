use super::*;
use era_cudart::memory::memory_copy_async;

impl GpuGKRStage1Output {
    pub(crate) fn empty_for_tests(context: &ProverContext) -> CudaResult<Self> {
        Ok(Self {
            tracing_ranges: Vec::new(),
            memory_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            witness_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            scratch_space_trace: None,
            lookup_mappings: GpuGKRLookupMappings {
                generic_family: None,
                range_check_16: None,
                timestamp: None,
                trace_len: 0,
                num_generic_sets: 0,
                has_decoder: false,
            },
        })
    }

    pub(crate) fn with_lookup_mappings_for_tests(
        context: &ProverContext,
        trace_len: usize,
        generic_sets: &[&[u32]],
        decoder: Option<&[u32]>,
        range_check_16_sets: &[&[u32]],
        timestamp_sets: &[&[u32]],
    ) -> CudaResult<Self> {
        fn flatten_columns(trace_len: usize, columns: &[&[u32]]) -> Vec<u32> {
            let mut flattened = Vec::with_capacity(trace_len * columns.len());
            for column in columns {
                assert_eq!(
                    column.len(),
                    trace_len,
                    "test lookup mapping column length mismatch"
                );
                flattened.extend_from_slice(column);
            }
            flattened
        }

        fn upload_columns(
            context: &ProverContext,
            trace_len: usize,
            columns: &[&[u32]],
        ) -> CudaResult<Option<DeviceAllocation<u32>>> {
            if columns.is_empty() {
                return Ok(None);
            }
            let flattened = flatten_columns(trace_len, columns);
            let mut device = context.alloc(flattened.len(), AllocationPlacement::BestFit)?;
            memory_copy_async(&mut device, &flattened, context.get_exec_stream())?;
            Ok(Some(device))
        }

        let mut generic_columns = generic_sets.to_vec();
        if let Some(decoder) = decoder {
            generic_columns.push(decoder);
        }

        let result = Self {
            tracing_ranges: Vec::new(),
            memory_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            witness_trace_holder: TraceHolder::new_without_cosets(
                1,
                0,
                0,
                0,
                0,
                TreesCacheMode::CacheNone,
                context,
            )?,
            scratch_space_trace: None,
            lookup_mappings: GpuGKRLookupMappings {
                generic_family: upload_columns(context, trace_len, &generic_columns)?,
                range_check_16: upload_columns(context, trace_len, range_check_16_sets)?,
                timestamp: upload_columns(context, trace_len, timestamp_sets)?,
                trace_len,
                num_generic_sets: generic_sets.len(),
                has_decoder: decoder.is_some(),
            },
        };
        context.get_exec_stream().synchronize()?;
        Ok(result)
    }
}
