use super::callbacks::Callbacks;
use super::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use super::stage_4::StageFourOutput;
use super::trace_holder::{allocate_tree_caps, flatten_tree_caps, transfer_tree_cap, CosetsHolder};
use super::{BF, E2, E4};
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{build_merkle_tree, Digest};
use crate::ops_complex::fold;
use crate::prover::precomputations::PRECOMPUTATIONS;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use fft::{
    bitreverse_enumeration_inplace, partial_ifft_natural_to_natural, GoodAllocator,
    LdePrecomputations,
};
use field::{Field, FieldExtension, Mersenne31Field};
use itertools::Itertools;
use prover::definitions::{FoldingDescription, Transcript};
use prover::transcript::Seed;
use std::iter;

pub(crate) struct FRIStep {
    pub ldes: Vec<DeviceAllocation<E4>>,
    pub trees: Vec<DeviceAllocation<Digest>>,
    pub tree_caps: Vec<HostAllocation<[Digest]>>,
}

impl FRIStep {
    pub fn get_tree_caps_accessors(&self) -> Vec<UnsafeAccessor<[Digest]>> {
        self.tree_caps
            .iter()
            .map(HostAllocation::get_accessor)
            .collect_vec()
    }
}

pub(crate) struct StageFiveOutput {
    pub(crate) fri_oracles: Vec<FRIStep>,
    pub(crate) last_fri_step_plain_leaf_values: Vec<HostAllocation<[E4]>>,
    pub(crate) final_monomials: HostAllocation<[E4]>,
}

impl StageFiveOutput {
    pub fn new<'a>(
        seed: &mut HostAllocation<Seed>,
        stage_4_output: &mut StageFourOutput,
        log_domain_size: u32,
        log_lde_factor: u32,
        folding_description: &FoldingDescription,
        num_queries: usize,
        lde_precomputations: &LdePrecomputations<impl GoodAllocator>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        assert_eq!(log_domain_size, stage_4_output.trace_holder.log_domain_size);
        let log_tree_cap_size = folding_description.total_caps_size_log2 as u32;
        let lde_factor = 1usize << log_lde_factor;
        let mut log_current_domain_size = log_domain_size;
        let oracles_count = folding_description.folding_sequence.len() - 1;
        let mut fri_oracles: Vec<FRIStep> = vec![];
        let mut last_fri_step_plain_leaf_values = Default::default();
        let stream = context.get_exec_stream();
        let seed_accessor = seed.get_mut_accessor();
        let taus_clone = lde_precomputations.domain_bound_precomputations[0]
            .as_ref()
            .unwrap()
            .taus
            .clone();
        let mut taus = unsafe { context.alloc_host_uninit_slice(taus_clone.len()) };
        let taus_accessor = taus.get_mut_accessor();
        let set_taus_fn = move || unsafe {
            taus_accessor.get_mut().copy_from_slice(&taus_clone);
        };
        callbacks.schedule(set_taus_fn, stream)?;
        for (i, &current_log_fold) in folding_description
            .folding_sequence
            .iter()
            .take(oracles_count)
            .enumerate()
        {
            let folding_degree_log2 = current_log_fold as u32;
            let log_folded_domain_size = log_current_domain_size - folding_degree_log2;
            let next_log_fold = folding_description.folding_sequence[i + 1] as u32;
            let log_num_leafs = log_folded_domain_size - next_log_fold;
            let mut ldes = Vec::with_capacity(lde_factor);
            for _ in 0..lde_factor {
                ldes.push(context.alloc(1 << log_folded_domain_size, AllocationPlacement::Bottom)?);
            }
            let folding_inputs = if i == 0 {
                match &stage_4_output.trace_holder.cosets {
                    CosetsHolder::Full { evaluations } => evaluations,
                    CosetsHolder::Single { .. } => unreachable!(),
                }
            } else {
                &fri_oracles[i - 1].ldes
            };
            let challenges_len = lde_factor * current_log_fold;
            let mut h_challenges = unsafe { context.alloc_host_uninit_slice(challenges_len) };
            let h_challenges_accessor = h_challenges.get_mut_accessor();
            let set_folding_challenges_fn = move || unsafe {
                Self::set_folding_challenges(
                    seed_accessor.get_mut(),
                    taus_accessor.get_mut(),
                    h_challenges_accessor.get_mut(),
                    current_log_fold,
                );
            };
            callbacks.schedule(set_folding_challenges_fn, stream)?;
            let mut d_challenges = context.alloc(challenges_len, AllocationPlacement::BestFit)?;
            memory_copy_async(
                &mut d_challenges,
                unsafe { h_challenges_accessor.get() },
                stream,
            )?;
            for ((folding_input, folding_output), challenges) in folding_inputs
                .iter()
                .zip(ldes.iter_mut())
                .zip(d_challenges.chunks(current_log_fold))
            {
                Self::fold_coset(
                    folding_degree_log2,
                    challenges,
                    folding_input,
                    folding_output,
                    context,
                )?;
            }
            d_challenges.free();
            let expose_all_leafs = if i == oracles_count - 1 {
                let log_bound = num_queries.next_power_of_two().trailing_zeros();
                log_num_leafs + 1 - log_lde_factor <= log_bound
            } else {
                false
            };
            let (trees, tree_caps) = if expose_all_leafs {
                let mut leaf_values = vec![];
                for d_coset in ldes.iter() {
                    let len = d_coset.len();
                    let mut h_coset = unsafe { context.alloc_host_uninit_slice(len) };
                    memory_copy_async(
                        unsafe { h_coset.get_mut_accessor().get_mut() },
                        d_coset,
                        stream,
                    )?;
                    leaf_values.push(h_coset);
                }
                last_fri_step_plain_leaf_values = leaf_values;
                let leaf_values_accessors = last_fri_step_plain_leaf_values
                    .iter()
                    .map(|x| x.get_accessor())
                    .collect_vec();
                let commit_fn = move || unsafe {
                    let mut transcript_input = vec![];
                    for values in leaf_values_accessors.iter() {
                        let it = values
                            .get()
                            .iter()
                            .flat_map(|x| x.into_coeffs_in_base().map(|y: BF| y.to_reduced_u32()));
                        transcript_input.extend(it);
                    }
                    Transcript::commit_with_seed(seed_accessor.get_mut(), &transcript_input);
                };
                callbacks.schedule(commit_fn, stream)?;
                (vec![], vec![])
            } else {
                let mut trees = Vec::with_capacity(lde_factor);
                for _ in 0..lde_factor {
                    trees.push(
                        context.alloc(1 << (log_num_leafs + 1), AllocationPlacement::Bottom)?,
                    );
                }
                let mut tree_caps = allocate_tree_caps(log_lde_factor, log_tree_cap_size, context);
                let next_log_fold = folding_description.folding_sequence[i + 1] as u32;
                let log_num_leafs = log_folded_domain_size - next_log_fold;
                assert!(log_tree_cap_size >= log_lde_factor);
                let log_coset_cap_size = log_tree_cap_size - log_lde_factor;
                for ((lde, tree), caps) in ldes
                    .iter()
                    .zip_eq(trees.iter_mut())
                    .zip_eq(tree_caps.iter_mut())
                {
                    let log_tree_len = log_num_leafs + 1;
                    let layers_count = log_num_leafs + 1 - log_coset_cap_size;
                    assert_eq!(tree.len(), 1 << log_tree_len);
                    let values = unsafe { lde.transmute() };
                    build_merkle_tree(
                        values,
                        tree,
                        next_log_fold + 2,
                        stream,
                        layers_count,
                        false,
                    )?;
                    transfer_tree_cap(tree, caps, log_lde_factor, log_tree_cap_size, stream)?;
                }
                let tree_caps_accessors = tree_caps
                    .iter()
                    .map(HostAllocation::get_accessor)
                    .collect_vec();
                let update_seed_fn = move || unsafe {
                    let input = flatten_tree_caps(&tree_caps_accessors).collect_vec();
                    Transcript::commit_with_seed(seed_accessor.get_mut(), &input);
                };
                callbacks.schedule(update_seed_fn, stream)?;
                (trees, tree_caps)
            };
            let oracle = FRIStep {
                ldes,
                trees,
                tree_caps,
            };
            fri_oracles.push(oracle);
            log_current_domain_size = log_folded_domain_size;
        }
        assert_eq!(
            log_current_domain_size as usize,
            folding_description.final_monomial_degree_log2
                + folding_description.folding_sequence.last().unwrap()
        );
        let final_monomials = {
            let log_folding_degree = *folding_description.folding_sequence.last().unwrap() as u32;
            let challenges_len = log_folding_degree as usize;
            let mut h_challenges = unsafe { context.alloc_host_uninit_slice(challenges_len) };
            let h_challenges_accessor = h_challenges.get_mut_accessor();
            let set_folding_challenges_fn = move || unsafe {
                Self::set_folding_challenges(
                    seed_accessor.get_mut(),
                    &mut taus_accessor.get_mut()[..1],
                    h_challenges_accessor.get_mut(),
                    log_folding_degree as usize,
                );
            };
            callbacks.schedule(set_folding_challenges_fn, stream)?;
            let mut d_challenges = context.alloc(challenges_len, AllocationPlacement::BestFit)?;
            memory_copy_async(
                &mut d_challenges,
                unsafe { h_challenges_accessor.get() },
                stream,
            )?;
            let log_folded_domain_size = log_current_domain_size - log_folding_degree;
            let folded_domain_size = 1 << log_folded_domain_size;
            let mut d_folded_domain =
                context.alloc(folded_domain_size, AllocationPlacement::BestFit)?;
            Self::fold_coset(
                log_folding_degree,
                &d_challenges,
                &fri_oracles.last().unwrap().ldes[0],
                &mut d_folded_domain,
                context,
            )?;
            let mut h_folded_domain =
                unsafe { context.alloc_host_uninit_slice(folded_domain_size) };
            let h_folded_domain_accessor = h_folded_domain.get_mut_accessor();
            memory_copy_async(
                unsafe { h_folded_domain_accessor.get_mut() },
                &d_folded_domain,
                stream,
            )?;
            log_current_domain_size -= log_folding_degree;
            let domain_size = 1 << log_current_domain_size;
            let mut monomials = unsafe { context.alloc_host_uninit_slice(domain_size) };
            let monomials_accessor = monomials.get_mut_accessor();
            let monomials_fn = move || unsafe {
                let h_folded_domain = h_folded_domain_accessor.get();
                let mut c0 = h_folded_domain.iter().map(|el| el.c0).collect_vec();
                let mut c1 = h_folded_domain.iter().map(|el| el.c1).collect_vec();
                assert_eq!(c0.len(), domain_size);
                assert_eq!(c1.len(), domain_size);
                bitreverse_enumeration_inplace(&mut c0);
                bitreverse_enumeration_inplace(&mut c1);
                Self::interpolate(&mut c0);
                Self::interpolate(&mut c1);
                let coeffs = c0
                    .into_iter()
                    .zip(c1.into_iter())
                    .map(|(c0, c1)| E4 { c0, c1 })
                    .collect_vec();
                monomials_accessor.get_mut().copy_from_slice(&coeffs);
                let mut transcript_input = vec![];
                let it = monomials_accessor
                    .get()
                    .iter()
                    .flat_map(|x| x.into_coeffs_in_base().map(|y: BF| y.to_reduced_u32()));
                transcript_input.extend(it);
                Transcript::commit_with_seed(seed_accessor.get_mut(), &transcript_input);
            };
            callbacks.schedule(monomials_fn, stream)?;
            monomials
        };
        assert_eq!(
            log_current_domain_size as usize,
            folding_description.final_monomial_degree_log2
        );
        let result = Self {
            fri_oracles,
            last_fri_step_plain_leaf_values,
            final_monomials,
        };
        Ok(result)
    }

    fn draw_challenge(seed: &mut Seed) -> E4 {
        let mut transcript_challenges =
            [0u32; 4usize.next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
        Transcript::draw_randomness(seed, &mut transcript_challenges);
        let coeffs = transcript_challenges
            .as_chunks::<4>()
            .0
            .iter()
            .next()
            .unwrap()
            .map(BF::from_nonreduced_u32);
        E4::from_coeffs_in_base(&coeffs)
    }

    fn set_folding_challenges(
        seed: &mut Seed,
        taus: &mut [E2],
        challenges: &mut [E4],
        log_degree: usize,
    ) {
        assert_eq!(challenges.len(), taus.len() * log_degree);
        let mut challenge = Self::draw_challenge(seed);
        let challenge_powers = iter::once(challenge)
            .chain((1..log_degree).map(|_| {
                challenge.square();
                challenge
            }))
            .collect_vec();
        for (tau, chunk) in taus.iter_mut().zip(challenges.chunks_mut(log_degree)) {
            let mut tau_inv = tau.inverse().unwrap();
            for (challenge, mut power) in chunk.iter_mut().zip(challenge_powers.iter().copied()) {
                power.mul_assign_by_base(&tau_inv);
                *challenge = power;
                tau_inv.square();
                tau.square();
            }
        }
    }

    fn fold_coset(
        log_degree: u32,
        challenges: &DeviceSlice<E4>,
        input: &DeviceAllocation<E4>,
        output: &mut DeviceAllocation<E4>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let log_degree = log_degree as usize;
        assert_eq!(log_degree, challenges.len());
        let domain_size = input.len();
        assert!(domain_size.is_power_of_two());
        let log_domain_size = domain_size.trailing_zeros();
        let mut temp_alloc: Option<DeviceAllocation<E4>> = None;
        let mut output = Some(output);
        let stream = context.get_exec_stream();
        for i in 0..log_degree {
            let log_current_domain_size = log_domain_size - i as u32;
            let log_next_domain_size = log_current_domain_size - 1;
            let mut temp_src = temp_alloc.take();
            let src = if let Some(temp) = temp_src.as_mut() {
                temp
            } else {
                input
            };
            let dst = if i == log_degree - 1 {
                output.take().unwrap()
            } else {
                temp_alloc =
                    Some(context.alloc(1 << log_next_domain_size, AllocationPlacement::BestFit)?);
                temp_alloc.as_mut().unwrap()
            };
            fold(&challenges[i], src, dst, 0, stream)?;
        }
        Ok(())
    }

    fn interpolate(c0: &mut [E2]) {
        let twiddles = &PRECOMPUTATIONS.inverse_twiddles[..c0.len() / 2];
        partial_ifft_natural_to_natural(c0, E2::ONE, twiddles);
        if c0.len() > 1 {
            let n_inv = Mersenne31Field(c0.len() as u32).inverse().unwrap();
            let mut i = 0;
            let work_size = c0.len();
            while i < work_size {
                c0[i].mul_assign_by_base(&n_inv);
                i += 1;
            }
        }
    }
}
