use proc_macro2::TokenStream;
use quote::quote;

use crate::mersenne_wrapper::MersenneWrapper;

pub fn generate_whir_common<MW: MersenneWrapper>(max_fold_steps: usize) -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let quartic_one = MW::quartic_one();
    let max_high_powers = if max_fold_steps > 0 {
        1usize << (max_fold_steps - 1)
    } else {
        1
    };
    let field_struct = MW::field_struct();

    // read_and_batch_leaf ops
    let from_raw = MW::field_from_reduced_raw_repr(quote! { raw });
    let mul_term_base = MW::mul_assign_by_base(quote! { term }, quote! { base_val });
    let add_acc0_term = MW::add_assign(quote! { *acc0 }, quote! { term });
    let add_acc1_term = MW::add_assign(quote! { *acc1 }, quote! { term });

    // whir sumcheck ops
    let add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { c1 });
    let add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { c2 });
    let add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let mul_claim_alpha = MW::mul_assign(quote! { new_claim }, quote! { alpha });
    let add_claim_c1 = MW::add_assign(quote! { new_claim }, quote! { c1 });
    let add_claim_c0 = MW::add_assign(quote! { new_claim }, quote! { c0 });

    // gamma power / fold coset ops
    let mul_pow_gen = MW::mul_assign(quote! { pow }, quote! { set_gen_inv });
    let mul_gamma_pow = MW::mul_assign(quote! { gamma_pow }, quote! { gamma });
    let sub_t_b = MW::sub_assign(quote! { t }, quote! { b });
    let mul_t_challenge = MW::mul_assign(quote! { t }, quote! { challenge });
    let mul_t_root = MW::mul_assign_by_base(quote! { t }, quote! { root });
    let add_t_a = MW::add_assign(quote! { t }, quote! { a });
    let add_t_b = MW::add_assign(quote! { t }, quote! { b });
    let mul_t_half = MW::mul_assign_by_base(quote! { t }, quote! { #field_struct::HALF });
    let mul_root_offset = MW::mul_assign(quote! { root }, quote! { high_powers_offset });
    let square_root_inv = MW::square(quote! { root_inv });

    let sub_oma_alpha = MW::sub_assign(quote! { one_minus_alpha }, quote! { alpha });
    let double_two_alpha = MW::double(quote! { two_alpha });
    let mul_two_a_zi_zi = MW::mul_assign(quote! { two_a_zi }, quote! { zi });
    let add_eq_two_a_zi = MW::add_assign(quote! { eq }, quote! { two_a_zi });
    let sub_eq_zi = MW::sub_assign(quote! { eq }, quote! { zi });
    let mul_prefactor_eq = MW::mul_assign(quote! { acc.z_initial_prefactor }, quote! { eq });
    let mul_two_a_s_s = MW::mul_assign(quote! { two_a_s }, quote! { s });
    let add_eq_two_a_s = MW::add_assign(quote! { eq }, quote! { two_a_s });
    let sub_eq_s = MW::sub_assign(quote! { eq }, quote! { s });
    let mul_entry_prefactor_eq = MW::mul_assign(quote! { entry.prefactor }, quote! { eq });
    let square_current_scalar = MW::square(quote! { entry.current_scalar });

    quote! {
        #[inline(always)]
        pub fn compute_tree_index(
            query_index: usize,
            num_cosets: usize,
            num_cosets_log2: usize,
            coset_tree_size: usize,
        ) -> usize {
            let coset_index = query_index & (num_cosets - 1);
            let internal_index = query_index >> num_cosets_log2;
            if num_cosets == 1 {
                internal_index
            } else {
                let coset_dest = coset_index.reverse_bits()
                    >> (usize::BITS as usize - num_cosets_log2);
                coset_dest * coset_tree_size + internal_index
            }
        }

        #[inline(always)]
        pub fn verify_whir_sumcheck_step<I: NonDeterminismSource, E: ErrorCreator>(
            ts: &mut TranscriptState,
            claim: #quartic_struct,
            round: usize,
        ) -> Result<(#quartic_struct, #quartic_struct), E::Error> {
            const WHIR_SC_DATA_WORDS: usize = 3 * EXT_DEGREE;
            const WHIR_SC_COMMIT_BUF: usize = {
                let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_SC_DATA_WORDS;
                (total + ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
                    / ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
                    * ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
            };

            let mut buf = CommitBuf::<WHIR_SC_COMMIT_BUF>::new();
            {
                let mut i = 0;
                while i < WHIR_SC_DATA_WORDS {
                    buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }

            let coeffs: [#quartic_struct; 3] = unsafe {
                *buf.data_as::<[#quartic_struct; 3]>(1).as_ptr()
            };
            let (c0, c1, c2) = (coeffs[0], coeffs[1], coeffs[2]);

            let p0 = c0;
            let mut p1 = c0;
            #add_p1_c1;
            #add_p1_c2;
            let mut sum = p0;
            #add_sum_p1;
            if sum != claim {
                return Err(E::whir_sumcheck_failed(round));
            }

            ts.commit(&mut buf, WHIR_SC_DATA_WORDS);

            let alpha = draw_single_field_el(ts);

            let mut new_claim = c2;
            #mul_claim_alpha;
            #add_claim_c1;
            #mul_claim_alpha;
            #add_claim_c0;

            Ok((new_claim, alpha))
        }

        #[inline(always)]
        pub fn materialize_gamma_powers<const N: usize>(
            gamma: #quartic_struct,
        ) -> [#quartic_struct; N] {
            debug_assert!(N > 1);

            let mut powers: LazyVec<#quartic_struct, N> = LazyVec::new();
            powers.push(#quartic_one);
            let mut i = 1;
            let mut gamma_pow = gamma;
            while i < N - 1 {
                powers.push(gamma_pow);
                #mul_gamma_pow;
                i += 1;
            }
            powers.push(gamma_pow);

            unsafe { powers.into_array() }
        }

        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub fn fold_coset(
            evals: &[#quartic_struct],
            num_rounds: usize,
            folding_challenges: &[#quartic_struct],
            mut root_inv: #field_struct,
            high_powers_offsets: &[#field_struct],
            buf_a: &mut [#quartic_struct],
            buf_b: &mut [#quartic_struct],
        ) -> #quartic_struct {
            debug_assert!(num_rounds == 0 || high_powers_offsets.len() >= 1 << (num_rounds - 1));
            let mut round = 0;
            while round < num_rounds {
                let half = 1 << (num_rounds - round - 1);
                let challenge = unsafe { *folding_challenges.get_unchecked(round) };

                let src: &[#quartic_struct] = if round == 0 {
                    evals
                } else if round % 2 == 1 {
                    unsafe { core::slice::from_raw_parts(buf_a.as_ptr(), half * 2) }
                } else {
                    unsafe { core::slice::from_raw_parts(buf_b.as_ptr(), half * 2) }
                };
                let dst: &mut [#quartic_struct] = if round % 2 == 0 {
                    unsafe { core::slice::from_raw_parts_mut(buf_a.as_mut_ptr(), half) }
                } else {
                    unsafe { core::slice::from_raw_parts_mut(buf_b.as_mut_ptr(), half) }
                };

                let mut pair_idx = 0;
                while pair_idx < half {
                    let src_idx = pair_idx * 2;
                    let a = unsafe { *src.get_unchecked(src_idx) };
                    let b = unsafe { *src.get_unchecked(src_idx + 1) };

                    let mut t = a;
                    #sub_t_b;
                    #mul_t_challenge;

                    let mut root = root_inv;
                    let high_powers_offset = unsafe { *high_powers_offsets.get_unchecked(pair_idx) };
                    #mul_root_offset;
                    #mul_t_root;

                    #add_t_a;
                    #add_t_b;
                    #mul_t_half;

                    unsafe { *dst.get_unchecked_mut(pair_idx) = t; }
                    pair_idx += 1;
                }

                #square_root_inv;
                round += 1;
            }

            if num_rounds == 0 {
                unsafe { *evals.get_unchecked(0) }
            } else if num_rounds % 2 == 1 {
                unsafe { *buf_a.get_unchecked(0) }
            } else {
                unsafe { *buf_b.get_unchecked(0) }
            }
        }

        pub const MAX_HIGH_POWERS: usize = #max_high_powers;

        #[inline(always)]
        pub fn bitreverse_inplace<T: Copy>(arr: &mut [T]) {
            let n = arr.len();
            if n <= 1 {
                return;
            }
            let log_n = n.trailing_zeros();
            let mut i = 0;
            while i < n {
                let j = (i as u32).reverse_bits().wrapping_shr(32 - log_n) as usize;
                if i < j {
                    unsafe {
                        let tmp = *arr.get_unchecked(i);
                        *arr.get_unchecked_mut(i) = *arr.get_unchecked(j);
                        *arr.get_unchecked_mut(j) = tmp;
                    }
                }
                i += 1;
            }
        }

        /// Compute bit-reversed high powers of the set-generator inverse for fold_coset.
        #[inline(always)]
        pub fn compute_high_powers_offsets(
            fold_steps: usize,
            dst: &mut LazyVec<#field_struct, MAX_HIGH_POWERS>,
        ) {
            let count = 1usize << (fold_steps - 1);
            dst.push(#field_struct::ONE);
            let set_gen_inv = #field_struct::TWO_ADICITY_GENERATORS_INVERSED[fold_steps];
            let mut pow = set_gen_inv;
            let mut i = 1;
            while i < count {
                dst.push(pow);
                #mul_pow_gen;
                i += 1;
            }
            bitreverse_inplace(&mut dst.as_mut_slice()[..count]);
        }

        #[inline(always)]
        pub fn ext_from_raw_word_slice(words: &[u32]) -> #quartic_struct {
            debug_assert!(words.len() >= EXT_DEGREE);
            let raw = unsafe { (words.as_ptr() as *const [u32; EXT_DEGREE]).as_ref_unchecked() };
            ext_from_raw_words::<#field_struct, #quartic_struct, EXT_DEGREE>(raw)
        }

        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub unsafe fn read_and_batch_leaf<I: NonDeterminismSource>(
            hash_buf: &mut [u32],
            num_columns: usize,
            gamma_powers: &[#quartic_struct],
            gamma_offset: usize,
            acc0: &mut #quartic_struct,
            acc1: &mut #quartic_struct,
        ) {
            let mut col = 0;
            while col < num_columns {
                let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
                let idx = col * 2;

                let raw = read_reduced_field_el::<I>();
                *hash_buf.get_unchecked_mut(idx) = raw;
                let base_val = #from_raw;
                let mut term = gamma;
                #mul_term_base;
                #add_acc0_term;

                let raw = read_reduced_field_el::<I>();
                *hash_buf.get_unchecked_mut(idx + 1) = raw;
                let base_val = #from_raw;
                let mut term = gamma;
                #mul_term_base;
                #add_acc1_term;

                col += 1;
            }
        }

        #[inline(always)]
        pub fn fold_whir_accumulator<const MAX_POW: usize>(
            acc: &mut ::verifier_common::whir::WhirAccumulator<#quartic_struct, MAX_POW>,
            alpha: #quartic_struct,
            z_initial: &[#quartic_struct],
        ) {
            // eq(z, α) = (1-z)(1-α) + zα = (1-α) - z + 2αz
            // precompute (1-α) and 2α; each inner eq eval is 1 mul + 1 add + 1 sub.
            let mut one_minus_alpha = #quartic_one;
            #sub_oma_alpha;
            let mut two_alpha = alpha;
            #double_two_alpha;

            unsafe {
                let zi = *z_initial.get_unchecked(acc.z_initial_idx);
                let mut eq = one_minus_alpha;
                let mut two_a_zi = two_alpha;
                #mul_two_a_zi_zi;
                #add_eq_two_a_zi;
                #sub_eq_zi;
                #mul_prefactor_eq;
                acc.z_initial_idx += 1;
            }

            let n = acc.pow_entries.len();
            let mut i = 0;
            while i < n {
                unsafe {
                    let entry = acc.pow_entries.get_unchecked_mut(i);
                    let s = entry.current_scalar;
                    let mut eq = one_minus_alpha;
                    let mut two_a_s = two_alpha;
                    #mul_two_a_s_s;
                    #add_eq_two_a_s;
                    #sub_eq_s;
                    #mul_entry_prefactor_eq;
                    #square_current_scalar;
                }
                i += 1;
            }
        }

        #[inline(always)]
        pub fn push_whir_pow_entry<const MAX_POW: usize>(
            acc: &mut ::verifier_common::whir::WhirAccumulator<#quartic_struct, MAX_POW>,
            current_scalar: #quartic_struct,
            coefficient: #quartic_struct,
        ) {
            acc.pow_entries.push(::verifier_common::whir::WhirPowEntry {
                current_scalar,
                prefactor: #quartic_one,
                coefficient,
            });
        }

        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub unsafe fn process_oracle_query<I: NonDeterminismSource, E: ErrorCreator, const BUF_SIZE: usize, const LEAF_WORDS: usize>(
            hasher: &mut DelegatedBlake2sState,
            hash_buf: &mut ::verifier_common::blake2s_u32::AlignedArray64<core::mem::MaybeUninit<u32>, BUF_SIZE>,
            num_columns: usize,
            query_index: usize,
            depth: usize,
            cap: &[u32],
            gamma_powers: &[#quartic_struct],
            gamma_offset: usize,
            acc0: &mut #quartic_struct,
            acc1: &mut #quartic_struct,
            query: usize,
        ) -> Result<(), E::Error> {
            use ::verifier_common::whir::{hash_leaf_data_into_state, verify_merkle_path};

            let buf = hash_buf.assume_init_subarray_mut::<BUF_SIZE>();
            read_and_batch_leaf::<I>(
                &mut buf[..LEAF_WORDS], num_columns,
                gamma_powers, gamma_offset, acc0, acc1,
            );

            let block_end = LEAF_WORDS.next_multiple_of(
                ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS,
            );
            if block_end > LEAF_WORDS {
                hash_buf.zero_range(LEAF_WORDS, block_end);
            }
            let buf = hash_buf.assume_init_subarray::<BUF_SIZE>();
            hash_leaf_data_into_state(hasher, buf, LEAF_WORDS);
            if !verify_merkle_path::<I>(hasher, query_index, depth, cap) {
                return Err(E::whir_merkle_path_failed(query));
            }
            Ok(())
        }
    }
}
