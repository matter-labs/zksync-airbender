use super::context::ProverContext;
use super::stage_4::StageFourOutput;
use super::{BF, E2, E4};
use crate::blake2s::{build_merkle_tree, Digest};
use crate::ops_complex::fold;
use crate::prover::callbacks::Callbacks;
use crate::prover::trace_holder::{allocate_tree_caps, flatten_tree_caps, transfer_tree_caps};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, DeviceSlice};
use fft::{
    bitreverse_enumeration_inplace, partial_ifft_natural_to_natural, GoodAllocator,
    LdePrecomputations, Twiddles,
};
use field::{Field, FieldExtension, Mersenne31Field};
use itertools::Itertools;
use prover::definitions::{FoldingDescription, Transcript};
use prover::transcript::Seed;
use std::iter;
use std::ops::Deref;
use std::sync::{Arc, Mutex};

pub(crate) struct FRIStep<C: ProverContext> {
    pub ldes: Vec<C::Allocation<E4>>,
    pub trees: Vec<C::Allocation<Digest>>,
    pub tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
}

pub(crate) struct StageFiveOutput<'a, C: ProverContext> {
    pub(crate) fri_oracles: Vec<FRIStep<C>>,
    pub(crate) last_fri_step_plain_leaf_values: Arc<Vec<Vec<E4, C::HostAllocator>>>,
    pub(crate) final_monomials: Arc<Mutex<Vec<E4>>>,
    pub(crate) callbacks: Callbacks<'a>,
}

impl<'a, C: ProverContext> StageFiveOutput<'a, C> {
    pub fn new(
        seed: Arc<Mutex<Seed>>,
        stage_4_output: &StageFourOutput<C>,
        log_domain_size: u32,
        log_lde_factor: u32,
        folding_description: &FoldingDescription,
        num_queries: usize,
        lde_precomputations: &LdePrecomputations<impl GoodAllocator>,
        twiddles: &Twiddles<E2, impl GoodAllocator>,
        context: &C,
    ) -> CudaResult<Self>
    where
        C::HostAllocator: 'a,
    {
        assert_eq!(log_domain_size, stage_4_output.trace_holder.log_domain_size);
        let log_tree_cap_size = folding_description.total_caps_size_log2 as u32;
        let lde_factor = 1usize << log_lde_factor;
        let mut log_current_domain_size = log_domain_size;
        let oracles_count = folding_description.folding_sequence.len() - 1;
        let taus_ref = &lde_precomputations.domain_bound_precomputations[0]
            .as_ref()
            .unwrap()
            .taus;
        let mut taus = Vec::with_capacity_in(taus_ref.len(), C::HostAllocator::default());
        taus.extend_from_slice(taus_ref);
        let taus = Arc::new(Mutex::new(taus));
        let mut fri_oracles: Vec<FRIStep<C>> = vec![];
        let mut last_fri_step_plain_leaf_values = Default::default();
        let mut callbacks = Callbacks::new();
        let stream = context.get_exec_stream();
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
                ldes.push(context.alloc(1 << log_folded_domain_size)?);
            }
            let folding_inputs = if i == 0 {
                &stage_4_output.trace_holder.ldes
            } else {
                &fri_oracles[i - 1].ldes
            };
            let challenges_len = lde_factor * current_log_fold;
            let mut h_challenges =
                Vec::with_capacity_in(challenges_len, C::HostAllocator::default());
            unsafe { h_challenges.set_len(challenges_len) };
            let h_challenges = Arc::new(Mutex::new(h_challenges));
            let seed_clone = seed.clone();
            let taus_clone = taus.clone();
            let h_challenges_clone = h_challenges.clone();
            let set_folding_challenges_fn = move || {
                Self::set_folding_challenges(
                    &mut seed_clone.lock().unwrap(),
                    &mut taus_clone.lock().unwrap(),
                    &mut h_challenges_clone.lock().unwrap(),
                    current_log_fold,
                );
            };
            callbacks.schedule(set_folding_challenges_fn, stream)?;
            let mut d_challenges = context.alloc(challenges_len)?;
            memory_copy_async(
                &mut d_challenges,
                h_challenges.lock().unwrap().deref(),
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
                    let mut h_coset = Vec::with_capacity_in(len, C::HostAllocator::default());
                    unsafe { h_coset.set_len(len) };
                    memory_copy_async(&mut h_coset, d_coset, stream)?;
                    leaf_values.push(h_coset);
                }
                last_fri_step_plain_leaf_values = Arc::new(leaf_values);
                let leaf_values_clone = last_fri_step_plain_leaf_values.clone();
                let seed_clone = seed.clone();
                let commit_fn = move || {
                    let mut transcript_input = vec![];
                    for values in leaf_values_clone.iter() {
                        let it = values
                            .iter()
                            .flat_map(|x| x.into_coeffs_in_base().map(|y: BF| y.to_reduced_u32()));
                        transcript_input.extend(it);
                    }
                    Transcript::commit_with_seed(
                        &mut seed_clone.lock().unwrap(),
                        &transcript_input,
                    );
                };
                callbacks.schedule(commit_fn, stream)?;
                (vec![], Arc::new(vec![]))
            } else {
                let mut trees = Vec::with_capacity(lde_factor);
                for _ in 0..lde_factor {
                    trees.push(context.alloc(1 << (log_num_leafs + 1))?);
                }
                let mut tree_caps = allocate_tree_caps::<C>(log_lde_factor, log_tree_cap_size);
                let next_log_fold = folding_description.folding_sequence[i + 1] as u32;
                let log_num_leafs = log_folded_domain_size - next_log_fold;
                let log_cap_size = folding_description.total_caps_size_log2 as u32;
                assert!(log_cap_size >= log_lde_factor);
                let log_coset_cap_size = log_cap_size - log_lde_factor;
                for (lde, tree) in ldes.iter().zip(trees.iter_mut()) {
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
                }
                transfer_tree_caps(
                    &trees,
                    &mut tree_caps,
                    log_lde_factor,
                    log_tree_cap_size,
                    stream,
                )?;
                let tree_caps = Arc::new(tree_caps);
                let tree_caps_clone = tree_caps.clone();
                let seed_clone = seed.clone();
                let update_seed_fn = move || {
                    let input = flatten_tree_caps(&tree_caps_clone).collect_vec();
                    Transcript::commit_with_seed(&mut seed_clone.lock().unwrap(), &input);
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
            let mut h_challenges =
                Vec::with_capacity_in(challenges_len, C::HostAllocator::default());
            unsafe { h_challenges.set_len(challenges_len) };
            let h_challenges = Arc::new(Mutex::new(h_challenges));
            let seed_clone = seed.clone();
            let taus_clone = taus.clone();
            let h_challenges_clone = h_challenges.clone();
            let set_folding_challenges_fn = move || {
                Self::set_folding_challenges(
                    &mut seed_clone.lock().unwrap(),
                    &mut taus_clone.lock().unwrap()[..1],
                    &mut h_challenges_clone.lock().unwrap(),
                    log_folding_degree as usize,
                );
            };
            callbacks.schedule(set_folding_challenges_fn, stream)?;
            let mut d_challenges = context.alloc(challenges_len)?;
            memory_copy_async(
                &mut d_challenges,
                &h_challenges.lock().unwrap().deref(),
                stream,
            )?;
            let log_folded_domain_size = log_current_domain_size - log_folding_degree;
            let folded_domain_size = 1 << log_folded_domain_size;
            let mut d_folded_domain = context.alloc(folded_domain_size)?;
            Self::fold_coset(
                log_folding_degree,
                &d_challenges,
                &fri_oracles.last().unwrap().ldes[0],
                &mut d_folded_domain,
                context,
            )?;
            let mut h_folded_domain =
                Vec::with_capacity_in(folded_domain_size, C::HostAllocator::default());
            unsafe { h_folded_domain.set_len(folded_domain_size) };
            memory_copy_async(&mut h_folded_domain, d_folded_domain.deref(), stream)?;
            log_current_domain_size -= log_folding_degree;
            let domain_size = 1 << log_current_domain_size;
            let monomials = Arc::new(Mutex::new(vec![]));
            let monomials_clone = monomials.clone();
            let mut inverse_twiddles = Vec::with_capacity(twiddles.inverse_twiddles.len());
            inverse_twiddles.extend_from_slice(&twiddles.inverse_twiddles);
            let monomials_fn = move || {
                let mut monomials = monomials_clone.lock().unwrap();
                let mut c0 = Vec::with_capacity(domain_size);
                let mut c1 = Vec::with_capacity(domain_size);
                for el in h_folded_domain.iter() {
                    c0.push(el.c0);
                    c1.push(el.c1);
                }
                assert_eq!(c0.len(), domain_size);
                assert_eq!(c1.len(), domain_size);
                bitreverse_enumeration_inplace(&mut c0);
                bitreverse_enumeration_inplace(&mut c1);
                Self::interpolate(&mut c0, &inverse_twiddles);
                Self::interpolate(&mut c1, &inverse_twiddles);
                for (c0, c1) in c0.into_iter().zip(c1.into_iter()) {
                    let el = E4 { c0, c1 };
                    monomials.push(el);
                }
                assert_eq!(monomials.len(), domain_size);
                let mut transcript_input = vec![];
                let it = monomials
                    .iter()
                    .flat_map(|x| x.into_coeffs_in_base().map(|y: BF| y.to_reduced_u32()));
                transcript_input.extend(it);
                Transcript::commit_with_seed(&mut seed.lock().unwrap(), &transcript_input);
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
            callbacks,
        };
        Ok(result)
    }

    fn draw_challenge(seed: &mut Seed) -> E4 {
        let mut transcript_challenges =
            [0u32; 4usize.next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
        Transcript::draw_randomness(seed, &mut transcript_challenges);
        let coeffs = transcript_challenges
            .array_chunks::<4>()
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
        input: &C::Allocation<E4>,
        output: &mut C::Allocation<E4>,
        context: &C,
    ) -> CudaResult<()> {
        let log_degree = log_degree as usize;
        assert_eq!(log_degree, challenges.len());
        let domain_size = input.len();
        assert!(domain_size.is_power_of_two());
        let log_domain_size = domain_size.trailing_zeros();
        let mut temp_alloc: Option<C::Allocation<E4>> = None;
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
                temp_alloc = Some(context.alloc(1 << log_next_domain_size)?);
                temp_alloc.as_mut().unwrap()
            };
            fold(&challenges[i], src, dst, 0, stream)?;
        }
        Ok(())
    }

    fn interpolate(c0: &mut [E2], twiddles: &[E2]) {
        let twiddles = &twiddles[..c0.len() / 2];
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
