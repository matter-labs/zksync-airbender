use super::context::ProverContext;
use super::setup::SetupPrecomputations;
use super::stage_1::StageOneOutput;
pub(crate) use super::stage_2_kernels::*;
use super::trace_holder::{flatten_tree_caps, TraceHolder};
use super::{BF, E4};
use crate::device_structures::{DeviceMatrix, DeviceMatrixChunk, DeviceMatrixMut};
use crate::ops_simple::set_by_ref;
use crate::prover::arg_utils::LookupChallenges;
use crate::prover::callbacks::Callbacks;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::definitions::NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use field::{Field, FieldExtension};
use prover::definitions::Transcript;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::transcript::Seed;
use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::{Arc, Mutex};

pub(crate) struct StageTwoOutput<'a, C: ProverContext> {
    pub(crate) trace_holder: TraceHolder<BF, C>,
    pub(crate) lookup_challenges: Option<Arc<Mutex<Box<LookupChallenges, C::HostAllocator>>>>,
    pub(crate) last_row: Option<Arc<Vec<BF, C::HostAllocator>>>,
    pub(crate) offset_for_grand_product_poly: usize,
    pub(crate) offset_for_sum_over_delegation_poly: Option<usize>,
    pub(crate) callbacks: Option<Callbacks<'a>>,
}

impl<'a, C: ProverContext> StageTwoOutput<'a, C> {
    pub fn allocate_trace_evaluations(
        circuit: &CompiledCircuitArtifact<BF>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        context: &C,
    ) -> CudaResult<Self>
    where
        C::HostAllocator: 'a,
    {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let layout = circuit.stage_2_layout;
        let num_stage_2_cols = layout.total_width;
        let trace_holder = TraceHolder::allocate_only_evaluation(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            num_stage_2_cols,
            true,
            context,
        )?;
        Ok(Self {
            trace_holder,
            lookup_challenges: None,
            last_row: None,
            offset_for_grand_product_poly: 0,
            offset_for_sum_over_delegation_poly: None,
            callbacks: None,
        })
    }

    pub fn generate(
        &mut self,
        seed: Arc<Mutex<Seed>>,
        circuit: &CompiledCircuitArtifact<BF>,
        cached_data: &ProverCachedData,
        setup: &SetupPrecomputations<C>,
        stage_1_output: &mut StageOneOutput<C>,
        context: &C,
    ) -> CudaResult<()>
    where
        C::HostAllocator: 'a,
    {
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let layout = circuit.stage_2_layout;
        let num_stage_2_cols = layout.total_width;
        let mut callbacks = Callbacks::new();
        let lookup_challenges = Arc::new(Mutex::new(Box::<LookupChallenges, _>::new_in(
            Default::default(),
            C::HostAllocator::default(),
        )));
        let stream = context.get_exec_stream();
        let lookup_challenges_clone = lookup_challenges.clone();
        let seed_clone = seed.clone();
        let lookup_challenges_fn = move || {
            let mut transcript_challenges = [0u32;
                ((NUM_LOOKUP_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4)
                    .next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            let mut guard = seed_clone.lock().unwrap();
            Transcript::draw_randomness(&mut guard, &mut transcript_challenges);
            let mut it = transcript_challenges.array_chunks::<4>();
            let mut get_challenge =
                || E4::from_coeffs_in_base(&it.next().unwrap().map(BF::from_nonreduced_u32));
            let linearization_challenges = std::array::from_fn(|_| get_challenge());
            let gamma = get_challenge();
            let challenges = LookupChallenges {
                linearization_challenges,
                gamma,
            };
            let mut guard = lookup_challenges_clone.lock().unwrap();
            *guard.deref_mut().deref_mut() = challenges;
        };
        callbacks.schedule(lookup_challenges_fn, stream)?;
        let num_stage_2_bf_cols = layout.num_base_field_polys();
        let num_stage_2_e4_cols = layout.num_ext4_field_polys();
        assert_eq!(
            num_stage_2_cols,
            4 * (((num_stage_2_bf_cols + 3) / 4) + num_stage_2_e4_cols)
        );
        let setup_cols = DeviceMatrix::new(&setup.trace_holder.get_evaluations(), trace_len);
        let generic_lookup_mappings = stage_1_output.generic_lookup_mapping.take().unwrap();
        let d_generic_lookups_args_to_table_entries_map =
            DeviceMatrix::new(&generic_lookup_mappings, trace_len);
        let trace_holder = &mut self.trace_holder;
        let trace = trace_holder.get_evaluations_mut();
        let mut d_stage_2_cols = DeviceMatrixMut::new(trace, trace_len);
        let num_e4_scratch_elems = get_stage_2_e4_scratch_elems(trace_len, circuit);
        let mut d_alloc_e4_scratch = context.alloc(num_e4_scratch_elems)?;
        let cub_scratch_bytes = get_stage_2_cub_scratch_bytes(trace_len, num_stage_2_bf_cols)?;
        let mut d_alloc_scratch_for_cub_ops = context.alloc(cub_scratch_bytes)?;
        let num_bf_scratch_elems = get_stage_2_bf_scratch_elems(num_stage_2_bf_cols);
        let mut d_alloc_scratch_for_col_sums = context.alloc(num_bf_scratch_elems)?;
        let mut d_lookup_challenges = context.alloc(1)?;
        let guard = lookup_challenges.lock().unwrap();
        memory_copy_async(
            d_lookup_challenges.deref_mut(),
            slice::from_ref(guard.deref().deref()),
            stream,
        )?;
        drop(guard);
        self.lookup_challenges = Some(lookup_challenges);
        let d_witness_cols =
            DeviceMatrix::new(&stage_1_output.witness_holder.get_evaluations(), trace_len);
        let d_memory_cols =
            DeviceMatrix::new(&stage_1_output.memory_holder.get_evaluations(), trace_len);
        compute_stage_2_args_on_main_domain(
            &setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_generic_lookups_args_to_table_entries_map,
            &mut d_stage_2_cols,
            &mut d_alloc_e4_scratch,
            &mut d_alloc_scratch_for_cub_ops,
            &mut d_alloc_scratch_for_col_sums,
            &d_lookup_challenges[0],
            cached_data,
            circuit,
            circuit.total_tables_size,
            log_domain_size,
            stream,
        )?;
        drop(generic_lookup_mappings);
        trace_holder.allocate_to_full(context)?;
        trace_holder.extend_and_commit(0, context)?;
        trace_holder.produce_tree_caps(context)?;
        let mut d_last_row = context.alloc(num_stage_2_cols)?;
        let last_row_src =
            DeviceMatrixChunk::new(trace_holder.get_evaluations(), trace_len, trace_len - 1, 1);
        let mut las_row_dst = DeviceMatrixMut::new(&mut d_last_row, 1);
        set_by_ref(&last_row_src, &mut las_row_dst, stream)?;
        let mut last_row = Vec::with_capacity_in(num_stage_2_cols, C::HostAllocator::default());
        unsafe { last_row.set_len(num_stage_2_cols) };
        memory_copy_async(&mut last_row, d_last_row.deref(), stream)?;
        let last_row = Arc::new(last_row);
        let last_row_clone = last_row.clone();
        self.last_row = Some(last_row);
        let offset_for_grand_product_poly = layout
            .intermediate_polys_for_memory_argument
            .get_range(cached_data.offset_for_grand_product_accumulation_poly)
            .start;
        self.offset_for_grand_product_poly = offset_for_grand_product_poly;
        let offset_for_sum_over_delegation_poly =
            if cached_data.handle_delegation_requests || cached_data.process_delegations {
                Some(cached_data.delegation_processing_aux_poly.start())
            } else {
                None
            };
        self.offset_for_sum_over_delegation_poly = offset_for_sum_over_delegation_poly;
        let has_delegation_processing_aux_poly = circuit
            .stage_2_layout
            .delegation_processing_aux_poly
            .is_some();
        let tree_caps = trace_holder.get_tree_caps();
        let update_seed_fn = move || {
            let mut transcript_input = vec![];
            transcript_input.extend(flatten_tree_caps(&tree_caps));
            transcript_input.extend(
                Self::get_grand_product_accumulator(offset_for_grand_product_poly, &last_row_clone)
                    .into_coeffs_in_base()
                    .iter()
                    .map(BF::to_reduced_u32),
            );
            if has_delegation_processing_aux_poly {
                transcript_input.extend(
                    Self::get_sum_over_delegation_poly(
                        offset_for_sum_over_delegation_poly,
                        &last_row_clone,
                    )
                    .unwrap_or_default()
                    .into_coeffs_in_base()
                    .iter()
                    .map(BF::to_reduced_u32),
                );
            }
            Transcript::commit_with_seed(&mut seed.lock().unwrap(), &transcript_input);
        };
        callbacks.schedule(update_seed_fn, stream)?;
        self.callbacks = Some(callbacks);
        Ok(())
    }

    pub fn get_grand_product_accumulator(offset: usize, last_row: &[BF]) -> E4 {
        E4::from_coeffs_in_base(&last_row[offset..offset + 4])
    }

    pub fn get_sum_over_delegation_poly(offset: Option<usize>, last_row: &[BF]) -> Option<E4> {
        offset.map(|o| {
            let coeffs = &last_row[o..o + 4];
            let mut value = E4::from_coeffs_in_base(coeffs);
            value.negate();
            value
        })
    }
}
