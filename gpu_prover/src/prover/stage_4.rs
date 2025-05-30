use super::{BF, E2, E4};
use crate::barycentric::{
    batch_barycentric_eval, get_batch_eval_temp_storage_sizes, precompute_lagrange_coeffs,
};
use crate::blake2s::build_merkle_tree;
use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::ops_complex::{bit_reverse_in_place, transpose};
use crate::prover::callbacks::Callbacks;
use crate::prover::context::ProverContext;
use crate::prover::setup::SetupPrecomputations;
use crate::prover::stage_1::StageOneOutput;
use crate::prover::stage_2::StageTwoOutput;
use crate::prover::stage_3::StageThreeOutput;
use crate::prover::stage_4_kernels::{
    compute_deep_denom_at_z_on_main_domain, compute_deep_quotient_on_main_domain,
    get_e4_scratch_count_for_deep_quotiening, get_metadata, ChallengesTimesEvals,
    NonWitnessChallengesAtZOmega,
};
use crate::prover::trace_holder::{extend_trace, flatten_tree_caps, TraceHolder};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::{GoodAllocator, Twiddles};
use field::{Field, FieldExtension};
use itertools::Itertools;
use prover::definitions::FoldingDescription;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;
use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::{Arc, Mutex};

pub(crate) struct StageFourOutput<'a, C: ProverContext> {
    pub(crate) trace_holder: TraceHolder<E4, C>,
    pub(crate) callbacks: Callbacks<'a>,
    pub(crate) values_at_z: Arc<Vec<E4, C::HostAllocator>>,
}

impl<'a, C: ProverContext> StageFourOutput<'a, C> {
    pub fn new(
        seed: Arc<Mutex<Seed>>,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        cached_data: &ProverCachedData,
        twiddles: &Twiddles<E2, impl GoodAllocator>,
        setup: &SetupPrecomputations<C>,
        stage_1_output: &StageOneOutput<C>,
        stage_2_output: &StageTwoOutput<C>,
        stage_3_output: &StageThreeOutput<C>,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        folding_description: &FoldingDescription,
        context: &C,
    ) -> CudaResult<Self>
    where
        C::HostAllocator: 'a,
    {
        const COSET_INDEX: usize = 0;
        let trace_len = circuit.trace_len;
        assert!(trace_len.is_power_of_two());
        let log_domain_size = trace_len.trailing_zeros();
        let log_fold_by = folding_description.folding_sequence[0] as u32;
        let mut trace_holder = TraceHolder::new(
            log_domain_size,
            log_lde_factor,
            log_fold_by,
            log_tree_cap_size,
            1,
            false,
            context,
        )?;
        let mut callbacks = Callbacks::new();
        let lde_factor = 1 << log_lde_factor;
        let num_evals_at_z = circuit.num_openings_at_z();
        let num_evals_at_z_omega = circuit.num_openings_at_z_omega();
        let num_evals = num_evals_at_z + num_evals_at_z_omega;
        let mut vectorized_ldes = vec![];
        for _ in 0..lde_factor {
            vectorized_ldes.push(context.alloc(4 * trace_len)?);
        }
        let mut values_at_z = Vec::with_capacity_in(num_evals, C::HostAllocator::default());
        unsafe { values_at_z.set_len(num_evals) };
        let stream = context.get_exec_stream();
        let h_z = Arc::new(Mutex::new(Box::new_in(
            E4::ZERO,
            C::HostAllocator::default(),
        )));
        let seed_clone = seed.clone();
        let h_z_clone = h_z.clone();
        let get_z = move || {
            let mut transcript_challenges =
                [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(
                seed_clone.lock().unwrap().deref_mut(),
                &mut transcript_challenges,
            );
            let coeffs = transcript_challenges
                .array_chunks::<4>()
                .next()
                .unwrap()
                .map(BF::from_nonreduced_u32);
            *h_z_clone.lock().unwrap().deref_mut().deref_mut() = E4::from_coeffs_in_base(&coeffs);
        };
        callbacks.schedule(get_z, stream)?;
        let coset = E2::ONE;
        let decompression_factor = None;
        let num_evals_at_z = circuit.num_openings_at_z();
        let num_evals_at_z_omega = circuit.num_openings_at_z_omega();
        let num_evals = num_evals_at_z + num_evals_at_z_omega;
        let row_chunk_size = 2048; // tunable for performance, 2048 is decent
        let mut d_alloc_z = context.alloc(1)?;
        memory_copy_async(
            &mut d_alloc_z,
            slice::from_ref(h_z.lock().unwrap().deref().deref()),
            &context.get_exec_stream(),
        )?;
        let mut d_alloc_evals = context.alloc(num_evals)?;
        let (partial_reduce_temp_elems, final_cub_reduce_temp_bytes) =
            get_batch_eval_temp_storage_sizes(&circuit, trace_len as u32, row_chunk_size)?;
        let mut d_alloc_temp_storage_partial_reduce = context.alloc(partial_reduce_temp_elems)?;
        let mut d_alloc_temp_storage_final_cub_reduce =
            context.alloc(final_cub_reduce_temp_bytes)?;
        let mut d_common_factor_storage = context.alloc(1)?;
        let mut d_lagrange_coeffs = context.alloc(trace_len)?;
        let d_setup_cols = DeviceMatrix::new(
            setup.trace_holder.get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_witness_cols = DeviceMatrix::new(
            stage_1_output
                .witness_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_memory_cols = DeviceMatrix::new(
            stage_1_output
                .memory_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_stage_2_cols = DeviceMatrix::new(
            stage_2_output
                .trace_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let d_composition_col = DeviceMatrix::new(
            stage_3_output
                .trace_holder
                .get_coset_evaluations(COSET_INDEX),
            trace_len,
        );
        let stream = context.get_exec_stream();
        precompute_lagrange_coeffs(
            &d_alloc_z[0],
            &mut d_common_factor_storage[0],
            coset,
            decompression_factor,
            &mut d_lagrange_coeffs,
            stream,
        )?;
        batch_barycentric_eval(
            &d_setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_stage_2_cols,
            &d_composition_col,
            &d_lagrange_coeffs,
            &mut d_alloc_temp_storage_partial_reduce,
            &mut d_alloc_temp_storage_final_cub_reduce,
            d_alloc_evals.deref_mut(),
            decompression_factor,
            &cached_data,
            circuit,
            row_chunk_size,
            log_domain_size,
            stream,
        )?;
        memory_copy_async(&mut values_at_z, d_alloc_evals.deref(), &stream)?;
        let seed_clone = seed.clone();
        let values_at_z = Arc::new(values_at_z);
        let values_at_z_clone = values_at_z.clone();
        let alpha = Arc::new(Mutex::new(E4::ZERO));
        let alpha_clone = alpha.clone();
        let get_alpha = move || {
            let transcript_input = values_at_z_clone
                .iter()
                .map(|el| el.into_coeffs_in_base())
                .flatten()
                .map(|el: BF| el.to_reduced_u32())
                .collect_vec();
            let mut seed = seed_clone.lock().unwrap();
            Transcript::commit_with_seed(&mut seed, &transcript_input);
            let mut transcript_challenges =
                [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(&mut seed, &mut transcript_challenges);
            let alpha_coeffs = transcript_challenges
                .array_chunks::<4>()
                .next()
                .unwrap()
                .map(BF::from_nonreduced_u32);
            *alpha_clone.lock().unwrap() = E4::from_coeffs_in_base(&alpha_coeffs);
        };
        callbacks.schedule(get_alpha, stream)?;
        let mut d_denom_at_z = context.alloc(trace_len)?;
        compute_deep_denom_at_z_on_main_domain(
            &mut d_denom_at_z,
            &d_alloc_z[0],
            log_domain_size,
            false,
            &stream,
        )?;
        let e4_scratch_elems = get_e4_scratch_count_for_deep_quotiening();
        let mut h_e4_scratch = Vec::with_capacity_in(e4_scratch_elems, C::HostAllocator::default());
        unsafe { h_e4_scratch.set_len(e4_scratch_elems) };
        let h_e4_scratch = Arc::new(Mutex::new(h_e4_scratch));
        let h_challenges_times_evals = Arc::new(Mutex::new(Box::new_in(
            ChallengesTimesEvals::default(),
            C::HostAllocator::default(),
        )));
        let h_non_witness_challenges_at_z_omega = Arc::new(Mutex::new(Box::new_in(
            NonWitnessChallengesAtZOmega::default(),
            C::HostAllocator::default(),
        )));
        let values_at_z_clone = values_at_z.clone();
        let alpha_clone = alpha.clone();
        let h_e4_scratch_clone = h_e4_scratch.clone();
        let h_challenges_times_evals_clone = h_challenges_times_evals.clone();
        let h_non_witness_challenges_at_z_omega_clone = h_non_witness_challenges_at_z_omega.clone();
        let cached_data_clone = cached_data.clone();
        let twiddles_omega_inv = twiddles.omega_inv;
        let circuit_clone = circuit.clone();
        let get_challenges = move || {
            let _ = get_metadata(
                &values_at_z_clone,
                *alpha_clone.lock().unwrap().deref(),
                twiddles_omega_inv,
                &cached_data_clone,
                &circuit_clone,
                &mut h_e4_scratch_clone.lock().unwrap().deref_mut(),
                &mut h_challenges_times_evals_clone.lock().unwrap(),
                &mut h_non_witness_challenges_at_z_omega_clone.lock().unwrap(),
            );
        };
        callbacks.schedule(get_challenges, stream)?;
        let mut d_e4_scratch = context.alloc(e4_scratch_elems)?;
        let mut d_challenges_times_evals = context.alloc(1)?;
        let mut d_non_witness_challenges_at_z_omega = context.alloc(1)?;
        memory_copy_async(
            &mut d_e4_scratch,
            h_e4_scratch.lock().unwrap().deref(),
            stream,
        )?;
        memory_copy_async(
            &mut d_challenges_times_evals,
            slice::from_ref(h_challenges_times_evals.lock().unwrap().deref().deref()),
            stream,
        )?;
        memory_copy_async(
            &mut d_non_witness_challenges_at_z_omega,
            slice::from_ref(
                h_non_witness_challenges_at_z_omega
                    .lock()
                    .unwrap()
                    .deref()
                    .deref(),
            ),
            stream,
        )?;
        let mut d_quotient = DeviceMatrixMut::new(&mut vectorized_ldes[COSET_INDEX], trace_len);
        let metadata = get_metadata(
            &vec![E4::ZERO; num_evals],
            E4::ZERO,
            twiddles.omega_inv,
            &cached_data,
            &circuit,
            &mut vec![E4::ZERO; e4_scratch_elems],
            &mut ChallengesTimesEvals::default(),
            &mut NonWitnessChallengesAtZOmega::default(),
        );
        compute_deep_quotient_on_main_domain(
            metadata,
            &d_setup_cols,
            &d_witness_cols,
            &d_memory_cols,
            &d_stage_2_cols,
            &d_composition_col,
            &d_denom_at_z,
            &mut d_e4_scratch,
            &d_challenges_times_evals[0],
            &d_non_witness_challenges_at_z_omega[0],
            &mut d_quotient,
            &cached_data,
            &circuit,
            log_domain_size,
            false,
            &stream,
        )?;
        extend_trace(
            &mut vectorized_ldes,
            COSET_INDEX,
            log_domain_size,
            log_lde_factor,
            context.get_exec_stream(),
            context.get_aux_stream(),
            context.get_device_properties(),
        )?;
        assert!(log_tree_cap_size >= log_lde_factor);
        let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
        let log_fold_by = folding_description.folding_sequence[0] as u32;
        let layers_count = log_domain_size + 1 - log_fold_by - log_coset_tree_cap_size;
        for ((vectorized_lde, lde), tree) in vectorized_ldes
            .iter()
            .zip(trace_holder.ldes.iter_mut())
            .zip(trace_holder.trees.iter_mut())
        {
            transpose(
                &DeviceMatrix::new(vectorized_lde, trace_len),
                &mut DeviceMatrixMut::new(unsafe { lde.transmute_mut() }, 4),
                stream,
            )?;
            bit_reverse_in_place(lde.deref_mut(), stream)?;
            build_merkle_tree(
                unsafe { lde.transmute_mut() },
                tree,
                log_fold_by + 2,
                stream,
                layers_count,
                false,
            )?;
        }
        trace_holder.produce_tree_caps(context)?;
        let tree_caps = trace_holder.get_tree_caps();
        let update_seed_fn = move || {
            let input = flatten_tree_caps(&tree_caps).collect_vec();
            Transcript::commit_with_seed(&mut seed.lock().unwrap(), &input);
        };
        callbacks.schedule(update_seed_fn, stream)?;
        let result = Self {
            trace_holder,
            callbacks,
            values_at_z,
        };
        Ok(result)
    }
}
