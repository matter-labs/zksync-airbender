use super::context::ProverContext;
use super::setup::SetupPrecomputations;
use super::stage_1::StageOneOutput;
use super::stage_2::StageTwoOutput;
use super::stage_3_kernels::*;
use super::{BF, E2, E4};
use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::prover::arg_utils::LookupChallenges;
use crate::prover::callbacks::Callbacks;
use crate::prover::trace_holder::{flatten_tree_caps, TraceHolder};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::{
    materialize_powers_serial_starting_with_one, GoodAllocator, LdePrecomputations, Twiddles,
};
use field::{Field, FieldExtension};
use itertools::Itertools;
use prover::definitions::ExternalValues;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::stage3::AlphaPowersLayout;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;
use std::alloc::Global;
use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::{Arc, Mutex};

pub(crate) struct StageThreeOutput<'a, C: ProverContext> {
    pub(crate) trace_holder: TraceHolder<BF, C>,
    pub(crate) callbacks: Callbacks<'a>,
}

impl<'a, C: ProverContext> StageThreeOutput<'a, C> {
    pub fn new(
        seed: Arc<Mutex<Seed>>,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        cached_data: &ProverCachedData,
        lde_precomputations: &LdePrecomputations<impl GoodAllocator>,
        twiddles: &Twiddles<E2, impl GoodAllocator>,
        external_values: ExternalValues,
        setup: &SetupPrecomputations<C>,
        stage_1_output: &StageOneOutput<C>,
        stage_2_output: &StageTwoOutput<C>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        context: &C,
    ) -> CudaResult<Self>
    where
        C::HostAllocator: 'a,
    {
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
        let mut callbacks = Callbacks::new();
        let stream = context.get_exec_stream();
        let alpha_powers_layout =
            AlphaPowersLayout::new(&circuit, cached_data.num_stage_3_quotient_terms);
        let alpha_powers_count = alpha_powers_layout.precomputation_size;
        let tau = lde_precomputations.domain_bound_precomputations[COSET_INDEX]
            .as_ref()
            .unwrap()
            .coset_offset;
        let mut h_alpha_powers =
            Vec::with_capacity_in(alpha_powers_count, C::HostAllocator::default());
        unsafe { h_alpha_powers.set_len(alpha_powers_count) };
        let h_beta_powers = Box::new_in([E4::ZERO; BETA_POWERS_COUNT], C::HostAllocator::default());
        let mut h_helpers = Vec::with_capacity_in(MAX_HELPER_VALUES, C::HostAllocator::default());
        unsafe { h_helpers.set_len(MAX_HELPER_VALUES) };
        let h_constants_times_challenges = Box::new_in(
            ConstantsTimesChallenges::default(),
            C::HostAllocator::default(),
        );
        let h_alpha_powers = Arc::new(Mutex::new(h_alpha_powers));
        let h_beta_powers = Arc::new(Mutex::new(h_beta_powers));
        let h_helpers = Arc::new(Mutex::new(h_helpers));
        let h_constants_times_challenges = Arc::new(Mutex::new(h_constants_times_challenges));
        let seed_clone = seed.clone();
        let h_alpha_powers_clone = h_alpha_powers.clone();
        let h_beta_powers_clone = h_beta_powers.clone();
        let h_helpers_clone = h_helpers.clone();
        let h_constants_times_challenges_clone = h_constants_times_challenges.clone();
        let lookup_challenges_clone = stage_2_output.lookup_challenges.clone();
        let stage_2_last_row_clone = stage_2_output.last_row.as_ref().unwrap().clone();
        let stage_2_offset_for_grand_product_poly = stage_2_output.offset_for_grand_product_poly;
        let offset_for_sum_over_delegation_poly =
            stage_2_output.offset_for_sum_over_delegation_poly;
        let cached_data_clone = cached_data.clone();
        let public_inputs = stage_1_output.get_public_inputs();
        let external_values_clone = external_values.clone();
        let circuit_clone = circuit.clone();
        let twiddles_omega = twiddles.omega;
        let twiddles_omega_inv = twiddles.omega_inv;
        let get_challenges_and_helpers_fn = move || {
            let mut transcript_challenges =
                [0u32; (2usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(
                &mut seed_clone.lock().unwrap(),
                &mut transcript_challenges,
            );
            let mut it = transcript_challenges.array_chunks::<4>();
            let mut get_challenge =
                || E4::from_coeffs_in_base(&it.next().unwrap().map(BF::from_nonreduced_u32));
            let alpha = get_challenge();
            let beta = get_challenge();
            let mut alpha_powers =
                materialize_powers_serial_starting_with_one::<_, Global>(alpha, alpha_powers_count);
            alpha_powers.reverse();
            let beta_powers =
                materialize_powers_serial_starting_with_one::<_, Global>(beta, BETA_POWERS_COUNT);
            h_alpha_powers_clone
                .lock()
                .unwrap()
                .copy_from_slice(&alpha_powers);
            h_beta_powers_clone
                .lock()
                .unwrap()
                .copy_from_slice(&beta_powers);
            let grand_product_accumulator = StageTwoOutput::<C>::get_grand_product_accumulator(
                stage_2_offset_for_grand_product_poly,
                &stage_2_last_row_clone,
            );
            let sum_over_delegation_poly = StageTwoOutput::<C>::get_sum_over_delegation_poly(
                offset_for_sum_over_delegation_poly,
                &stage_2_last_row_clone,
            )
            .unwrap_or_default();
            let mut helpers = Vec::with_capacity(MAX_HELPER_VALUES);
            let _ = Metadata::new(
                &alpha_powers,
                &beta_powers,
                tau,
                twiddles_omega,
                twiddles_omega_inv,
                &lookup_challenges_clone.as_ref().unwrap().lock().unwrap(),
                &cached_data_clone,
                &circuit_clone,
                &external_values_clone,
                &public_inputs.lock().unwrap(),
                grand_product_accumulator,
                sum_over_delegation_poly,
                log_domain_size,
                &mut helpers,
                &mut h_constants_times_challenges_clone.lock().unwrap(),
            );
            h_helpers_clone.lock().unwrap().copy_from_slice(&helpers);
        };
        callbacks.schedule(get_challenges_and_helpers_fn, stream)?;
        let mut d_alpha_powers = context.alloc(alpha_powers_count)?;
        let mut d_beta_powers = context.alloc(BETA_POWERS_COUNT)?;
        let mut d_helpers = context.alloc(MAX_HELPER_VALUES)?;
        let mut d_constants_times_challenges_sum = context.alloc(1)?;
        memory_copy_async(
            d_alpha_powers.deref_mut(),
            h_alpha_powers.lock().unwrap().deref(),
            stream,
        )?;
        memory_copy_async(
            d_beta_powers.deref_mut(),
            h_beta_powers.lock().unwrap().deref().deref(),
            stream,
        )?;
        memory_copy_async(
            d_helpers.deref_mut(),
            h_helpers.lock().unwrap().deref(),
            stream,
        )?;
        memory_copy_async(
            d_constants_times_challenges_sum.deref_mut(),
            slice::from_ref(h_constants_times_challenges.lock().unwrap().deref().deref()),
            stream,
        )?;
        let metadata = Metadata::new(
            &vec![E4::ZERO; alpha_powers_count],
            &[E4::ZERO; BETA_POWERS_COUNT],
            tau,
            twiddles.omega,
            twiddles.omega_inv,
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
        let tree_caps = trace_holder.get_tree_caps();
        let update_seed_fn = move || {
            let input = flatten_tree_caps(&tree_caps).collect_vec();
            Transcript::commit_with_seed(&mut seed.lock().unwrap(), &input);
        };
        callbacks.schedule(update_seed_fn, stream)?;
        Ok(Self {
            trace_holder,
            callbacks,
        })
    }
}
