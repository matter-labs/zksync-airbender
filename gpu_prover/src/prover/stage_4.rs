use super::callbacks::Callbacks;
use super::context::{HostAllocation, ProverContext};
use super::setup::SetupPrecomputations;
use super::stage_1::StageOneOutput;
use super::stage_2::StageTwoOutput;
use super::stage_3::StageThreeOutput;
use super::stage_4_kernels::{
    compute_deep_denom_at_z_on_main_domain, compute_deep_quotient_on_main_domain,
    get_e4_scratch_count_for_deep_quotiening, get_metadata, ChallengesTimesEvals,
    NonWitnessChallengesAtZOmega,
};
use super::trace_holder::{
    allocate_tree_caps, compute_coset_evaluations, split_evaluations_pair, transfer_tree_cap,
    CosetsHolder, TraceHolder, TreesHolder,
};
use super::{BF, E2, E4};
use crate::allocator::tracker::AllocationPlacement;
use crate::barycentric::{
    batch_barycentric_eval, get_batch_eval_temp_storage_sizes, precompute_lagrange_coeffs,
};
use crate::blake2s::build_merkle_tree;
use crate::device_structures::{DeviceMatrix, DeviceMatrixMut};
use crate::ops_complex::{bit_reverse_in_place, transpose};
use crate::prover::precomputations::PRECOMPUTATIONS;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use field::{Field, FieldExtension};
use itertools::Itertools;
use prover::definitions::FoldingDescription;
use prover::prover_stages::cached_data::ProverCachedData;
use prover::prover_stages::Transcript;
use prover::transcript::Seed;
use std::ops::DerefMut;
use std::slice;
use std::sync::Arc;

pub(crate) struct StageFourOutput {
    pub(crate) trace_holder: TraceHolder<E4>,
    pub(crate) values_at_z: HostAllocation<[E4]>,
}

impl StageFourOutput {
    pub fn new(
        seed: &mut HostAllocation<Seed>,
        circuit: &Arc<CompiledCircuitArtifact<BF>>,
        cached_data: &ProverCachedData,
        setup: &mut SetupPrecomputations,
        stage_1_output: &mut StageOneOutput,
        stage_2_output: &mut StageTwoOutput,
        stage_3_output: &mut StageThreeOutput,
        log_lde_factor: u32,
        log_tree_cap_size: u32,
        folding_description: &FoldingDescription,
        callbacks: &mut Callbacks,
        context: &ProverContext,
    ) -> CudaResult<Self> {
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
            true,
            false,
            false,
            context,
        )?;
        let seed_accessor = seed.get_mut_accessor();
        let lde_factor = 1 << log_lde_factor;
        let num_evals_at_z = circuit.num_openings_at_z();
        let num_evals_at_z_omega = circuit.num_openings_at_z_omega();
        let num_evals = num_evals_at_z + num_evals_at_z_omega;
        let mut vectorized_ldes = vec![];
        for _ in 0..lde_factor {
            vectorized_ldes.push(context.alloc(4 * trace_len, AllocationPlacement::BestFit)?);
        }
        let stream = context.get_exec_stream();
        let mut values_at_z = unsafe { context.alloc_host_uninit_slice(num_evals) };
        let values_at_z_accessor = values_at_z.get_mut_accessor();
        let mut h_z = unsafe { context.alloc_host_uninit::<E4>() };
        let h_z_accessor = h_z.get_mut_accessor();
        let get_z = move || unsafe {
            let mut transcript_challenges =
                [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(seed_accessor.get_mut(), &mut transcript_challenges);
            let coeffs = transcript_challenges
                .as_chunks::<4>()
                .0
                .iter()
                .next()
                .unwrap()
                .map(BF::from_nonreduced_u32);
            h_z_accessor.set(E4::from_coeffs_in_base(&coeffs));
        };
        callbacks.schedule(get_z, stream)?;
        let coset = E2::ONE;
        let decompression_factor = None;
        let num_evals_at_z = circuit.num_openings_at_z();
        let num_evals_at_z_omega = circuit.num_openings_at_z_omega();
        let num_evals = num_evals_at_z + num_evals_at_z_omega;
        let row_chunk_size = 2048; // tunable for performance, 2048 is decent
        let mut d_alloc_z = context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut d_alloc_z,
            slice::from_ref(unsafe { h_z_accessor.get() }),
            &context.get_exec_stream(),
        )?;
        let mut d_alloc_evals = context.alloc(num_evals, AllocationPlacement::BestFit)?;
        let (partial_reduce_temp_elems, final_cub_reduce_temp_bytes) =
            get_batch_eval_temp_storage_sizes(&circuit, trace_len as u32, row_chunk_size)?;
        let mut d_alloc_temp_storage_partial_reduce =
            context.alloc(partial_reduce_temp_elems, AllocationPlacement::BestFit)?;
        let mut d_alloc_temp_storage_final_cub_reduce =
            context.alloc(final_cub_reduce_temp_bytes, AllocationPlacement::BestFit)?;
        let mut d_common_factor_storage = context.alloc(1, AllocationPlacement::BestFit)?;
        let mut d_lagrange_coeffs = context.alloc(trace_len, AllocationPlacement::BestFit)?;
        let d_setup_cols = DeviceMatrix::new(
            setup
                .trace_holder
                .get_coset_evaluations(COSET_INDEX, context)?,
            trace_len,
        );
        let d_witness_cols = DeviceMatrix::new(
            stage_1_output
                .witness_holder
                .get_coset_evaluations(COSET_INDEX, context)?,
            trace_len,
        );
        let d_memory_cols = DeviceMatrix::new(
            stage_1_output
                .memory_holder
                .get_coset_evaluations(COSET_INDEX, context)?,
            trace_len,
        );
        let d_stage_2_cols = DeviceMatrix::new(
            stage_2_output
                .trace_holder
                .get_coset_evaluations(COSET_INDEX, context)?,
            trace_len,
        );
        let d_composition_col = DeviceMatrix::new(
            stage_3_output
                .trace_holder
                .get_coset_evaluations(COSET_INDEX, context)?,
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
        memory_copy_async(
            unsafe { values_at_z_accessor.get_mut() },
            &d_alloc_evals,
            &stream,
        )?;
        let mut alpha = unsafe { context.alloc_host_uninit::<E4>() };
        let alpha_accessor = alpha.get_mut_accessor();
        let get_alpha = move || unsafe {
            let transcript_input = values_at_z_accessor
                .get()
                .iter()
                .map(|el| el.into_coeffs_in_base())
                .flatten()
                .map(|el: BF| el.to_reduced_u32())
                .collect_vec();
            let seed = seed_accessor.get_mut();
            Transcript::commit_with_seed(seed, &transcript_input);
            let mut transcript_challenges =
                [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(seed, &mut transcript_challenges);
            let alpha_coeffs = transcript_challenges
                .as_chunks::<4>()
                .0
                .iter()
                .next()
                .unwrap()
                .map(BF::from_nonreduced_u32);
            alpha_accessor.set(E4::from_coeffs_in_base(&alpha_coeffs));
        };
        callbacks.schedule(get_alpha, stream)?;
        let mut d_denom_at_z = context.alloc(trace_len, AllocationPlacement::BestFit)?;
        compute_deep_denom_at_z_on_main_domain(
            &mut d_denom_at_z,
            &d_alloc_z[0],
            log_domain_size,
            false,
            &stream,
        )?;
        let e4_scratch_elems = get_e4_scratch_count_for_deep_quotiening();
        let mut h_e4_scratch = unsafe { context.alloc_host_uninit_slice(e4_scratch_elems) };
        let h_e4_scratch_accessor = h_e4_scratch.get_mut_accessor();
        let mut h_challenges_times_evals =
            unsafe { context.alloc_host_uninit::<ChallengesTimesEvals>() };
        let h_challenges_times_evals_accessor = h_challenges_times_evals.get_mut_accessor();
        let mut h_non_witness_challenges_at_z_omega =
            unsafe { context.alloc_host_uninit::<NonWitnessChallengesAtZOmega>() };
        let h_non_witness_challenges_at_z_omega_accessor =
            h_non_witness_challenges_at_z_omega.get_mut_accessor();
        let cached_data_clone = cached_data.clone();
        let omega_inv = PRECOMPUTATIONS.omegas_inv[log_domain_size as usize];
        let circuit_clone = circuit.clone();
        let get_challenges = move || unsafe {
            let _ = get_metadata(
                values_at_z_accessor.get(),
                *alpha_accessor.get(),
                omega_inv,
                &cached_data_clone,
                &circuit_clone,
                h_e4_scratch_accessor.get_mut(),
                h_challenges_times_evals_accessor.get_mut(),
                h_non_witness_challenges_at_z_omega_accessor.get_mut(),
            );
        };
        callbacks.schedule(get_challenges, stream)?;
        let mut d_e4_scratch = context.alloc(e4_scratch_elems, AllocationPlacement::BestFit)?;
        let mut d_challenges_times_evals = context.alloc(1, AllocationPlacement::BestFit)?;
        let mut d_non_witness_challenges_at_z_omega =
            context.alloc(1, AllocationPlacement::BestFit)?;
        memory_copy_async(
            &mut d_e4_scratch,
            unsafe { h_e4_scratch_accessor.get() },
            stream,
        )?;
        memory_copy_async(
            &mut d_challenges_times_evals,
            slice::from_ref(unsafe { h_challenges_times_evals_accessor.get() }),
            stream,
        )?;
        memory_copy_async(
            &mut d_non_witness_challenges_at_z_omega,
            slice::from_ref(unsafe { h_non_witness_challenges_at_z_omega_accessor.get() }),
            stream,
        )?;
        let mut d_quotient = DeviceMatrixMut::new(&mut vectorized_ldes[COSET_INDEX], trace_len);
        let metadata = get_metadata(
            &vec![E4::ZERO; num_evals],
            E4::ZERO,
            omega_inv,
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
        assert_eq!(log_lde_factor, 1);
        let (src, dst) = split_evaluations_pair(&mut vectorized_ldes, COSET_INDEX);
        compute_coset_evaluations(
            src,
            dst,
            COSET_INDEX,
            log_domain_size,
            log_lde_factor,
            true,
            context,
        )?;
        assert!(log_tree_cap_size >= log_lde_factor);
        let log_coset_tree_cap_size = log_tree_cap_size - log_lde_factor;
        let log_fold_by = folding_description.folding_sequence[0] as u32;
        let layers_count = log_domain_size + 1 - log_fold_by - log_coset_tree_cap_size;
        let mut tree_caps = allocate_tree_caps(log_lde_factor, log_tree_cap_size, context);
        for (((vectorized_lde, lde), tree), caps) in vectorized_ldes
            .iter()
            .zip_eq(match &mut trace_holder.cosets {
                CosetsHolder::Full { evaluations } => evaluations.iter_mut(),
                CosetsHolder::Single { .. } => unreachable!(),
            })
            .zip_eq(match &mut trace_holder.trees {
                TreesHolder::Device { trees } => trees.iter_mut(),
                TreesHolder::None => unreachable!(),
            })
            .zip_eq(tree_caps.iter_mut())
        {
            transpose(
                &DeviceMatrix::new(vectorized_lde, trace_len),
                &mut DeviceMatrixMut::new(unsafe { lde.transmute_mut() }, 4),
                stream,
            )?;
            bit_reverse_in_place(lde.deref_mut(), stream)?;
            build_merkle_tree(
                unsafe { lde.transmute() },
                tree,
                log_fold_by + 2,
                stream,
                layers_count,
                false,
            )?;
            transfer_tree_cap(tree, caps, log_lde_factor, log_tree_cap_size, stream)?;
        }
        trace_holder.tree_caps = Some(tree_caps);
        let update_seed_fn = trace_holder.get_update_seed_fn(seed);
        callbacks.schedule(update_seed_fn, stream)?;
        let result = Self {
            trace_holder,
            values_at_z,
        };
        Ok(result)
    }
}
