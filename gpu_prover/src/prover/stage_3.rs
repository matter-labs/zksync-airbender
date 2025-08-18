use super::arg_utils::LookupChallenges;
use super::callbacks::Callbacks;
use super::context::{HostAllocation, ProverContext};
use super::setup::SetupPrecomputations;
use super::stage_1::StageOneOutput;
use super::stage_2::StageTwoOutput;
use super::stage_3_kernels::*;
use super::trace_holder::TraceHolder;
use super::{BF, E4};
use crate::allocator::tracker::AllocationPlacement;
use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::prover::precomputations::PRECOMPUTATIONS;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::{materialize_powers_serial_starting_with_one, GoodAllocator, LdePrecomputations};
use field::{Field, FieldExtension};
use prover::definitions::ExternalValues;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::stage3::AlphaPowersLayout;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;
use std::alloc::Global;
use std::slice;
use std::sync::Arc;

pub(crate) struct StageThreeOutput {
    pub(crate) trace_holder: TraceHolder<BF>,
}

impl StageThreeOutput {
    pub fn new(
        seed: &mut HostAllocation<Seed>,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        cached_data: &ProverCachedData,
        lde_precomputations: &LdePrecomputations<impl GoodAllocator>,
        external_values: ExternalValues,
        setup: &SetupPrecomputations,
        stage_1_output: &StageOneOutput,
        stage_2_output: &StageTwoOutput,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        callbacks: &mut Callbacks,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        const COSET_INDEX: usize = 1;
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let mut trace_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            0,
            log_tree_cap_size,
            4,
            true,
            context,
        )?;
        let stream = context.get_exec_stream();
        let seed_accessor = seed.get_mut_accessor();
        let alpha_powers_layout =
            AlphaPowersLayout::new(&circuit, cached_data.num_stage_3_quotient_terms);
        let alpha_powers_count = alpha_powers_layout.precomputation_size;
        let tau = lde_precomputations.domain_bound_precomputations[COSET_INDEX]
            .as_ref()
            .unwrap()
            .coset_offset;
        let mut h_alpha_powers = unsafe { context.alloc_host_uninit_slice(alpha_powers_count) };
        let h_alpha_powers_accessor = h_alpha_powers.get_mut_accessor();
        let mut h_beta_powers = unsafe { context.alloc_host_uninit_slice(BETA_POWERS_COUNT) };
        let h_beta_powers_accessor = h_beta_powers.get_mut_accessor();
        let mut h_helpers = unsafe { context.alloc_host_uninit_slice(MAX_HELPER_VALUES) };
        let h_helpers_accessor = h_helpers.get_mut_accessor();
        let mut h_constants_times_challenges =
            unsafe { context.alloc_host_uninit::<ConstantsTimesChallenges>() };
        let h_constants_times_challenges_accessor = h_constants_times_challenges.get_mut_accessor();
        let stage_2_lookup_challenges_accessor = stage_2_output
            .lookup_challenges
            .as_ref()
            .unwrap()
            .get_accessor();
        let stage_2_last_row_accessor = stage_2_output.last_row.as_ref().unwrap().get_accessor();
        let stage_2_offset_for_grand_product_poly = stage_2_output.offset_for_grand_product_poly;
        let offset_for_sum_over_delegation_poly =
            stage_2_output.offset_for_sum_over_delegation_poly;
        let cached_data_clone = cached_data.clone();
        let public_inputs_accessor = stage_1_output
            .public_inputs
            .as_ref()
            .unwrap()
            .get_accessor();
        let external_values_clone = external_values.clone();
        let circuit_clone = circuit.clone();
        let omega_index = log_domain_size as usize;
        let omega = PRECOMPUTATIONS.omegas[omega_index];
        let omega_inv = PRECOMPUTATIONS.omegas_inv[omega_index];
        let get_challenges_and_helpers_fn = move || unsafe {
            let mut transcript_challenges =
                [0u32; (2usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(seed_accessor.get_mut(), &mut transcript_challenges);
            let mut it = transcript_challenges.as_chunks::<4>().0.iter();
            let mut get_challenge =
                || E4::from_coeffs_in_base(&it.next().unwrap().map(BF::from_nonreduced_u32));
            let alpha = get_challenge();
            let beta = get_challenge();
            let mut alpha_powers =
                materialize_powers_serial_starting_with_one::<_, Global>(alpha, alpha_powers_count);
            alpha_powers.reverse();
            let beta_powers =
                materialize_powers_serial_starting_with_one::<_, Global>(beta, BETA_POWERS_COUNT);
            h_alpha_powers_accessor
                .get_mut()
                .copy_from_slice(&alpha_powers);
            h_beta_powers_accessor
                .get_mut()
                .copy_from_slice(&beta_powers);
            let stage_2_last_row = stage_2_last_row_accessor.get();
            let grand_product_accumulator = StageTwoOutput::get_grand_product_accumulator(
                stage_2_offset_for_grand_product_poly,
                stage_2_last_row,
            );
            let sum_over_delegation_poly = StageTwoOutput::get_sum_over_delegation_poly(
                offset_for_sum_over_delegation_poly,
                stage_2_last_row,
            )
            .unwrap_or_default();
            let mut helpers = Vec::with_capacity(MAX_HELPER_VALUES);
            let _ = Metadata::new(
                &alpha_powers,
                &beta_powers,
                tau,
                omega,
                omega_inv,
                stage_2_lookup_challenges_accessor.get(),
                &cached_data_clone,
                &circuit_clone,
                &external_values_clone,
                public_inputs_accessor.get(),
                grand_product_accumulator,
                sum_over_delegation_poly,
                log_domain_size,
                &mut helpers,
                h_constants_times_challenges_accessor.get_mut(),
            );
            h_helpers_accessor.get_mut().copy_from_slice(&helpers);
        };
        callbacks.schedule(get_challenges_and_helpers_fn, stream)?;
        let mut d_alpha_powers = context.alloc(alpha_powers_count, AllocationPlacement::BestFit)?;
        let mut d_beta_powers = context.alloc(BETA_POWERS_COUNT, AllocationPlacement::BestFit)?;
        let mut d_helpers = context.alloc(MAX_HELPER_VALUES, AllocationPlacement::BestFit)?;
        let mut d_constants_times_challenges_sum =
            context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut d_alpha_powers,
            unsafe { h_alpha_powers_accessor.get() },
            stream,
        )?;
        memory_copy_async(
            &mut d_beta_powers,
            unsafe { h_beta_powers_accessor.get() },
            stream,
        )?;
        memory_copy_async(&mut d_helpers, unsafe { h_helpers_accessor.get() }, stream)?;
        memory_copy_async(
            &mut d_constants_times_challenges_sum,
            slice::from_ref(unsafe { h_constants_times_challenges_accessor.get() }),
            stream,
        )?;
        let metadata = Metadata::new(
            &vec![E4::ZERO; alpha_powers_count],
            &[E4::ZERO; BETA_POWERS_COUNT],
            tau,
            omega,
            omega_inv,
            &LookupChallenges::default(),
            cached_data,
            &circuit,
            &external_values,
            &vec![BF::ZERO; circuit.public_inputs.len()],
            E4::ZERO,
            E4::ZERO,
            log_domain_size,
            &mut Vec::with_capacity(MAX_HELPER_VALUES),
            &mut ConstantsTimesChallenges::default(),
        );
        let d_setup_cols = DeviceMatrix::new(
            &setup.trace_holder.get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_witness_cols = DeviceMatrix::new(
            &stage_1_output
                .witness_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_memory_cols = DeviceMatrix::new(
            &stage_1_output
                .memory_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_stage_2_cols = DeviceMatrix::new(
            &stage_2_output
                .trace_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let mut d_quotient = DeviceMatrixMut::new(
            trace_holder.get_coset_evaluations_mut(COSET_INDEX),
            trace_len,
        );
        compute_stage_3_composition_quotient_on_coset(
            cached_data,
            &circuit,
            metadata,
            &d_setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_stage_2_cols,
            &d_alpha_powers,
            &d_beta_powers,
            &d_helpers,
            &d_constants_times_challenges_sum[0],
            &mut d_quotient,
            log_domain_size,
            stream,
        )?;
        trace_holder.extend_and_commit(COSET_INDEX, context)?;
        trace_holder.produce_tree_caps(context)?;
        let update_seed_fn = trace_holder.get_update_seed_fn(seed);
        callbacks.schedule(update_seed_fn, stream)?;
        Ok(Self { trace_holder })
    }
}
