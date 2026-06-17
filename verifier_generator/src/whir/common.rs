use proc_macro2::TokenStream;
use quote::quote;

use crate::field_wrapper::FieldWrapper;

pub fn generate_whir_common<MW: FieldWrapper>(max_fold_steps: usize) -> TokenStream {
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
    // let mul_term_base = MW::mul_assign_by_base(quote! { term }, quote! { base_val });
    // let add_acc0_term = MW::add_assign(quote! { *acc0 }, quote! { term });
    // let add_acc1_term = MW::add_assign(quote! { *acc1 }, quote! { term });

    let fma_into_acc_0 =
        MW::add_assign_product_with_base(quote! { *acc0 }, quote! { gamma }, quote! { base_val });
    let fma_into_acc_1 =
        MW::add_assign_product_with_base(quote! { *acc1 }, quote! { gamma }, quote! { base_val });

    // whir sumcheck ops
    let add_p1_c1 = MW::add_assign(quote! { p1 }, quote! { c1 });
    let add_p1_c2 = MW::add_assign(quote! { p1 }, quote! { c2 });
    let add_sum_p1 = MW::add_assign(quote! { sum }, quote! { p1 });
    let mul_claim_alpha = MW::mul_assign(quote! { new_claim }, quote! { alpha });
    let add_claim_c1 = MW::add_assign(quote! { new_claim }, quote! { c1 });
    let add_claim_c0 = MW::add_assign(quote! { new_claim }, quote! { c0 });

    // gamma power ops (shared by both encodings: used by materialize_gamma_powers
    // and compute_high_powers_offsets).
    let mul_pow_gen = MW::mul_assign(quote! { pow }, quote! { set_gen_inv });
    let mul_gamma_pow = MW::mul_assign(quote! { gamma_pow }, quote! { gamma });

    // The per-leaf fold helpers differ between coefficient and evaluation form.
    // Exactly one branch is emitted (compile-time `eval_leaves`), so the generated
    // verifier carries a single fold implementation with no runtime branching.
    let fold_helpers = build_fold_helpers::<MW>();

    // fold_whir_accumulator (eq trick from PR #273): eq(z, α) = (1-α) - z + 2αz
    let sub_oma_alpha = MW::sub_assign(quote! { one_minus_alpha }, quote! { alpha });
    let double_two_alpha = MW::double(quote! { two_alpha });
    let mul_two_a_zi_zi = MW::mul_assign(quote! { two_a_zi }, quote! { zi });
    let add_eq_two_a_zi = MW::add_assign(quote! { eq }, quote! { two_a_zi });
    let eq_add_two_a_zi =
        MW::add_assign_product(quote! { eq }, quote! { two_alpha }, quote! { zi });
    let sub_eq_zi = MW::sub_assign(quote! { eq }, quote! { zi });
    let mul_prefactor_eq = MW::mul_assign(quote! { acc.z_initial_prefactor }, quote! { eq });
    let mul_two_a_s_s = MW::mul_assign(quote! { two_a_s }, quote! { s });
    let add_eq_two_a_s = MW::add_assign(quote! { eq }, quote! { two_a_s });
    let sub_eq_s = MW::sub_assign(quote! { eq }, quote! { s });
    let eq_add_two_a_s = MW::add_assign_product(quote! { eq }, quote! { two_alpha }, quote! { s });
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
            nd_source: &mut I,
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
                    buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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

        #fold_helpers

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
            nd_source: &mut I,
        ) {
            let mut col = 0;
            while col < num_columns {
                let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
                let idx = col * 2;

                let raw = read_reduced_field_el::<I>(nd_source);
                *hash_buf.get_unchecked_mut(idx) = raw;
                let base_val = #from_raw;
                #fma_into_acc_0;

                // let mut term = gamma;
                // #mul_term_base;
                // #add_acc0_term;

                let raw = read_reduced_field_el::<I>(nd_source);
                *hash_buf.get_unchecked_mut(idx + 1) = raw;
                let base_val = #from_raw;
                #fma_into_acc_1;

                // let mut term = gamma;
                // #mul_term_base;
                // #add_acc1_term;

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
                // eq += 2 * alpha * zi

                // #eq_add_two_a_zi; // not beneficial

                let mut two_a_zi = two_alpha;
                #mul_two_a_zi_zi;
                #add_eq_two_a_zi;

                // eq -= zi
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
                    // eq += two_alpha * s

                    // #eq_add_two_a_s; // not beneficial

                    let mut two_a_s = two_alpha;
                    #mul_two_a_s_s;
                    #add_eq_two_a_s;

                    // eq -= s
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
            nd_source: &mut I,
        ) -> Result<(), E::Error> {
            use ::verifier_common::whir::{hash_leaf_data_into_state, verify_merkle_path};

            let buf = hash_buf.assume_init_subarray_mut::<BUF_SIZE>();
            read_and_batch_leaf::<I>(
                &mut buf[..LEAF_WORDS], num_columns,
                gamma_powers, gamma_offset, acc0, acc1, nd_source,
            );

            let block_end = LEAF_WORDS.next_multiple_of(
                ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS,
            );
            if block_end > LEAF_WORDS {
                hash_buf.zero_range(LEAF_WORDS, block_end);
            }
            let buf = hash_buf.assume_init_subarray::<BUF_SIZE>();
            hash_leaf_data_into_state(hasher, buf, LEAF_WORDS);
            if !verify_merkle_path::<I>(hasher, query_index, depth, cap, nd_source) {
                return Err(E::whir_merkle_path_failed(query));
            }
            Ok(())
        }
    }
}

/// Emits the per-leaf fold helper(s) for the active leaf encoding. The whole
/// generator is compiled either with or without `eval_leaves`, so exactly one
/// branch contributes to the generated verifier — there is no runtime dispatch
/// and the generated fold path is identical to the hand-written reference for
/// that encoding.
fn build_fold_helpers<MW: FieldWrapper>() -> TokenStream {
    let quartic_struct = MW::quartic_struct();
    let field_struct = MW::field_struct();
    if cfg!(feature = "eval_leaves") {
        // ---- evaluation form: fold_coset butterfly ----
        // fold_coset butterfly: t = (a - b)*challenge*root, then t = (t + a + b)/2
        let sub_t_b = MW::sub_assign(quote! { t }, quote! { b });
        let mul_t_challenge = MW::mul_assign(quote! { t }, quote! { challenge });
        let mul_t_root = MW::mul_assign_by_base(quote! { t }, quote! { root });
        let add_t_a = MW::add_assign(quote! { t }, quote! { a });
        let add_t_b = MW::add_assign(quote! { t }, quote! { b });
        let mul_t_half = MW::mul_assign_by_base(quote! { t }, quote! { #field_struct::HALF });
        let mul_root_offset = MW::mul_assign(quote! { root }, quote! { high_powers_offset });
        let square_root_inv = MW::square(quote! { root_inv });
        let _ = &field_struct;
        quote! {
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
        }
    } else {
        // ---- coefficient form (default): evals -> multilinear coeffs, then
        // evaluate with the monomial tensor of the folding challenges ----
        let quartic_one = MW::quartic_one();
        // evals_to_multilinear_coeffs: c_even = (a+b)/2, c_odd = (a-b)*root/2
        let even_add_b = MW::add_assign(quote! { c_even }, quote! { b });
        let even_mul_half =
            MW::mul_assign_by_base(quote! { c_even }, quote! { #field_struct::HALF });
        let odd_sub_b = MW::sub_assign(quote! { c_odd }, quote! { b });
        let odd_mul_root = MW::mul_assign_by_base(quote! { c_odd }, quote! { root });
        let odd_mul_half = MW::mul_assign_by_base(quote! { c_odd }, quote! { #field_struct::HALF });
        let mul_root_offset = MW::mul_assign(quote! { r }, quote! { hp_offset });
        let square_root_inv = MW::square(quote! { root_inv });
        // eval_multilinear_with_monomial_tensor: result += c * w
        let term_mul_weight = MW::mul_assign(quote! { term }, quote! { w });
        let result_add_term = MW::add_assign(quote! { result }, quote! { term });
        // precompute_monomial_tensor: w_alpha = w * alpha
        let walpha_mul_alpha = MW::mul_assign(quote! { w_alpha }, quote! { alpha });
        quote! {
        #[inline(always)]
        #[allow(clippy::too_many_arguments)]
        pub fn evals_to_multilinear_coeffs<const N: usize>(
            data: &mut [#quartic_struct],
            mut root_inv: #field_struct,
            high_powers_offsets: &[#field_struct],
            num_folding_rounds: usize,
            buf_a: &mut LazyVec<#quartic_struct, N>,
            buf_b: &mut LazyVec<#quartic_struct, N>,
        ) {
            let n = 1usize << num_folding_rounds;
            debug_assert_eq!(data.len(), n);
            debug_assert!(n <= N);
            if num_folding_rounds == 0 {
                return;
            }

            let mut stage = 0;
            while stage < num_folding_rounds {
                let src_ptr: *const #quartic_struct = if stage == 0 {
                    data.as_ptr()
                } else if stage % 2 == 1 {
                    buf_a.as_ptr()
                } else {
                    buf_b.as_ptr()
                };
                let dst_ptr: *mut #quartic_struct = if stage + 1 == num_folding_rounds {
                    data.as_mut_ptr()
                } else if stage % 2 == 0 {
                    buf_a.as_mut_ptr()
                } else {
                    buf_b.as_mut_ptr()
                };

                let num_existing = 1usize << stage;
                let block_len = n >> stage;
                let half = block_len / 2;

                let mut idx = 0;
                while idx < num_existing {
                    let base = idx * block_len;
                    let out_base = idx * half;
                    let linear_base = (idx | num_existing) * half;
                    let mut set_idx = 0;
                    while set_idx < half {
                        let a = unsafe { *src_ptr.add(base + 2 * set_idx) };
                        let b = unsafe { *src_ptr.add(base + 2 * set_idx + 1) };

                        // high_powers_offsets[0] == ONE, so skip the mul for set_idx=0.
                        let root = if set_idx == 0 {
                            root_inv
                        } else {
                            let hp_offset = unsafe {
                                *high_powers_offsets.get_unchecked(set_idx)
                            };
                            let mut r = root_inv;
                            #mul_root_offset;
                            r
                        };

                        let mut c_even = a;
                        #even_add_b;
                        #even_mul_half;

                        let mut c_odd = a;
                        #odd_sub_b;
                        #odd_mul_root;
                        #odd_mul_half;

                        unsafe { dst_ptr.add(out_base + set_idx).write(c_even); }
                        unsafe { dst_ptr.add(linear_base + set_idx).write(c_odd); }
                        set_idx += 1;
                    }
                    idx += 1;
                }

                // Skip the square on the final stage — root_inv is unused afterward.
                if stage + 1 < num_folding_rounds {
                    #square_root_inv;
                }
                stage += 1;
            }
        }


        #[inline(always)]
        pub fn precompute_monomial_tensor<const N: usize>(
            challenges: &[#quartic_struct],
            weights: &mut LazyVec<#quartic_struct, N>,
        ) {
            let k = challenges.len();
            let len = 1usize << k;
            debug_assert!(len <= N);
            unsafe { weights.set_unchecked(0, #quartic_one); }
            let mut j = 0;
            while j < k {
                let alpha = unsafe { *challenges.get_unchecked(j) };
                let bit = 1usize << j;
                let mut i = bit;
                while i > 0 {
                    i -= 1;
                    let w = unsafe { *weights.get_unchecked(i) };
                    let mut w_alpha = w;
                    #walpha_mul_alpha;
                    unsafe { weights.set_unchecked(i + bit, w_alpha); }
                }
                j += 1;
            }
            unsafe { weights.set_len(len); }
        }

        #[inline(always)]
        pub fn eval_multilinear_with_monomial_tensor(
            coeffs: &[#quartic_struct],
            weights: &[#quartic_struct],
        ) -> #quartic_struct {
            debug_assert_eq!(coeffs.len(), weights.len());
            let n = coeffs.len();
            let mut result = unsafe { *coeffs.get_unchecked(0) };
            let mut i = 1;
            while i < n {
                let mut term = unsafe { *coeffs.get_unchecked(i) };
                let w = unsafe { *weights.get_unchecked(i) };
                #term_mul_weight;
                #result_add_term;
                i += 1;
            }
            result
        }
        }
    }
}
