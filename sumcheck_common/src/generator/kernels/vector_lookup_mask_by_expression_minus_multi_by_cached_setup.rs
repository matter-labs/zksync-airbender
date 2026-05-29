use super::*;
use cs::definitions::gkr::NoFieldVectorLookupRelation;

pub(crate) fn generate_compute_fns<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &(GKRAddress, NoFieldVectorLookupRelation),
    setup: (GKRAddress, GKRAddress),
    output: [GKRAddress; 2],
    gate_idx: usize,
    layer_idx: usize,
    num_challenges: usize,
    base_field_scratch_space_size: usize,
    ext_field_scratch_space_size: usize,
    all_base_outputs: &BTreeSet<GKRAddress>,
    all_ext_outputs: &BTreeSet<GKRAddress>,
    pos_state: &BTreeMap<GKRAddress, SumcheckAddressState>,
    challenges: Vec<usize>,
) -> (TokenStream, TokenStream) {
    let (compute_fn_initial_round_id, compute_fn_id) = compute_fn_ids(gate_idx, layer_idx);

    let num_base_field_outputs = all_base_outputs.len();
    let num_ext_field_outputs = all_ext_outputs.len();

    assert_eq!(challenges.len(), 2);
    let num_term_challenge = challenges[0];
    let den_term_challenge = challenges[1];

    let num_output_to_read = all_ext_outputs
        .iter()
        .position(|el| *el == output[0])
        .expect("pos");
    let den_output_to_read = all_ext_outputs
        .iter()
        .position(|el| *el == output[1])
        .expect("pos");

    let mut explicit_acc_fn = quote! {};
    let mut quadratic_acc_fn = quote! {
        let mut acc = E::ZERO;
    };
    {
        if input.1.columns[0].constant != 0 {
            let c = input.1.columns[0].constant;
            explicit_acc_fn.extend(quote! {
                let mut acc = E::from_base(F::from_u32_unchecked(#c));
            });
        } else {
            explicit_acc_fn.extend(quote! {
                let mut acc = E::ZERO;
            });
        }
    }

    for (idx, column) in input.1.columns.iter().enumerate() {
        assert!(column.linear_terms.len() > 0);
        if idx == 0 {
            let mut acc_fn = quote! {};
            let (c, address) = column.linear_terms[0];
            let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
            assert!(c != 0);

            if c != 1 {
                acc_fn.extend(quote! {
                    let mut t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_base(&F::from_u32_unchecked(#c));
                });
            } else {
                acc_fn.extend(quote! {
                    let mut t = base_field_scratch[#input_scratch_to_use][subindex];
                });
            }

            for (c, address) in column.linear_terms[1..].iter().copied() {
                let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                assert!(c != 0);
                let cc = F::from_u32_unchecked(c);

                if cc == F::ONE {
                    acc_fn.extend(quote! {
                        t = t.add_other(&base_field_scratch[#input_scratch_to_use][subindex]);
                    });
                } else if cc == F::MINUS_ONE {
                    acc_fn.extend(quote! {
                        t = t.sub_other(&base_field_scratch[#input_scratch_to_use][subindex]);
                    });
                } else {
                    acc_fn.extend(quote! {
                        t = t.add_other(&base_field_scratch[#input_scratch_to_use][subindex].mul_by_base(&F::from_u32_unchecked(#c)));
                    });
                }
            }

            // finish first term - constant was already handled
            acc_fn.extend(quote! {
                acc = t.add_with_ext(&acc, base_repr_ctx);
            });
            quadratic_acc_fn.extend(acc_fn.clone());
            explicit_acc_fn.extend(acc_fn);
        } else {
            let mut acc_fn = quote! {};
            // we also need to multiply by challenges, and add constants if needed
            let (c, address) = column.linear_terms[0];
            let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
            assert!(c != 0);
            if c != 1 {
                acc_fn.extend(quote! {
                    let mut t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_base(&F::from_u32_unchecked(#c));
                });
            } else {
                acc_fn.extend(quote! {
                    let mut t = base_field_scratch[#input_scratch_to_use][subindex];
                });
            }

            quadratic_acc_fn.extend(acc_fn.clone());
            explicit_acc_fn.extend(acc_fn);

            if column.constant != 0 {
                let c = column.constant;
                explicit_acc_fn.extend(quote! {
                    t = t.add_base(&F::from_u32_unchecked(#c));
                });
            }

            for (c, address) in column.linear_terms[1..].iter().copied() {
                let mut acc_fn = quote! {};
                let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                assert!(c != 0);
                let cc = F::from_u32_unchecked(c);

                if cc == F::ONE {
                    acc_fn.extend(quote! {
                        t = t.add_other(&base_field_scratch[#input_scratch_to_use][subindex]);
                    });
                } else if cc == F::MINUS_ONE {
                    acc_fn.extend(quote! {
                        t = t.sub_other(&base_field_scratch[#input_scratch_to_use][subindex]);
                    });
                } else {
                    acc_fn.extend(quote! {
                        t = t.add_other(&base_field_scratch[#input_scratch_to_use][subindex].mul_by_base(&F::from_u32_unchecked(#c)));
                    });
                }

                quadratic_acc_fn.extend(acc_fn.clone());
                explicit_acc_fn.extend(acc_fn);

                if column.constant != 0 {
                    let c = column.constant;
                    explicit_acc_fn.extend(quote! {
                        t = t.add_base(&F::from_u32_unchecked(#c));
                    });
                }
            }

            // finish first term - constant was already handled
            let power_idx = idx - 1;
            quadratic_acc_fn.extend(quote! {
                let t = t.mul_by_ext(&lookup_alpha_powers[#power_idx], base_repr_ctx);
                acc.add_assign(&t);
            });
            explicit_acc_fn.extend(quote! {
                let t = t.mul_by_ext(&lookup_alpha_powers[#power_idx], base_repr_ctx);
                acc.add_assign(&t);
            });
        }
    }

    // mask/(input + gamma) - multiplicity/(cached_setup + gamma) -> ()

    let quadratic_only_fn_id = Ident::new(
        &format!(
            "compute_layer_{}_gate_{}_quadratic_part_only",
            layer_idx, gate_idx
        ),
        Span::call_site(),
    );
    let explicit_fn_id = Ident::new(
        &format!("compute_layer_{}_gate_{}_explicit", layer_idx, gate_idx),
        Span::call_site(),
    );

    let mask_scratch_idx = pos_state.get(&input.0).expect("pos").cache_pos;
    let multiplicity_scratch_idx = pos_state.get(&setup.0).expect("pos").cache_pos;
    let cached_setup_scratch_idx = pos_state.get(&setup.1).expect("pos").cache_pos;

    let quad_fn = quote! {
        #[inline(always)]
        fn #quadratic_only_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, const N: usize>(
            base_field_scratch: &[[S::BaseFieldInput; N]; #base_field_scratch_space_size],
            ext_field_scratch: &[[S::ExtFieldInput; N]; #ext_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(N > 0);
                core::hint::assert_unchecked(subindex < N);
            }
            // mask/(input + gamma) - multiplicity/(cached_setup + gamma) -> (mask * cached_input - multiplicity * input), (input * cached_setup)
            let input: E = {
                #quadratic_acc_fn

                acc
            };
            let mask = base_field_scratch[#mask_scratch_idx][subindex];
            let multiplicity = base_field_scratch[#multiplicity_scratch_idx][subindex];
            let cached_setup = ext_field_scratch[#cached_setup_scratch_idx][subindex];

            // TODO: consider if we can avoid extra multiplication
            let mut num = cached_setup.mul_by_ext(&sumcheck_challenges[#num_term_challenge], ext_repr_ctx);
            num = mask.mul_by_ext(&num, base_repr_ctx);
            let mut t = multiplicity.mul_by_ext(&input, base_repr_ctx);
            t.mul_assign(&sumcheck_challenges[#num_term_challenge]);
            num.sub_assign(&t);

            let mut den = cached_setup.mul_by_ext(&sumcheck_challenges[#den_term_challenge], ext_repr_ctx);
            den = mask.mul_by_ext(&den, base_repr_ctx);

            let mut result = num;
            result.add_assign(&den);

            result
        }
    };

    let explicit_fn = quote! {
        #[inline(always)]
        fn #explicit_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &[[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            ext_field_scratch: &[[S::ExtFieldInput; 2]; #ext_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(subindex < 2);
            }
            // mask/(input + gamma) - multiplicity/(cached_setup + gamma) -> (mask * (cached_setup + gamma) - multiplicity * (input + gamma)), ((input + gamma) * (cached_setup + gamma))
            let input: E = {
                #quadratic_acc_fn

                acc
            };
            let mask = base_field_scratch[#mask_scratch_idx][subindex];
            let multiplicity = base_field_scratch[#multiplicity_scratch_idx][subindex];
            let cached_setup = ext_field_scratch[#cached_setup_scratch_idx][subindex];

            let mut input_plus_gamma = input;
            input_plus_gamma.add_assign(lookup_gamma);
            let cached_setup_plus_gamma = cached_setup.add_with_ext(lookup_gamma, ext_repr_ctx);

            let mut num = mask.mul_by_ext(&cached_setup_plus_gamma, base_repr_ctx);
            let t = multiplicity.mul_by_ext(&input_plus_gamma, base_repr_ctx);
            num.sub_assign(&t);
            num.mul_assign(&sumcheck_challenges[#num_term_challenge]);

            let mut den = input_plus_gamma;
            den.mul_assign(&cached_setup_plus_gamma);
            den.mul_assign(&sumcheck_challenges[#den_term_challenge]);

            let mut result = num;
            result.add_assign(&den);

            result
        }
    };

    let compute_fn_initial_round = quote! {
        #explicit_fn

        #quad_fn

        #[inline(always)]
        pub fn #compute_fn_initial_round_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &[S::BaseFieldInput; #base_field_scratch_space_size],
            ext_field_scratch: &[S::ExtFieldInput; #ext_field_scratch_space_size],
            all_base_outputs: &[S::BaseInputAccessor; #num_base_field_outputs],
            all_ext_outputs: &[S::ExtInputAccessor; #num_ext_field_outputs],
            sumcheck_challenges: &[E; #num_challenges],
            external_challenges: &impl GKRExternalChallengesProvider<F, E>,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            row_index: usize,
        ) -> [E; 2] {
            let mut c0 = all_ext_outputs[#num_output_to_read].get_f0_only::<false>(row_index).mul_by_ext(&sumcheck_challenges[#num_term_challenge], ext_repr_ctx);
            c0.add_assign(&all_ext_outputs[#den_output_to_read].get_f0_only::<false>(row_index).mul_by_ext(&sumcheck_challenges[#den_term_challenge], ext_repr_ctx));

            let mut c1 = unsafe {
                let base_field_scratch = core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; #base_field_scratch_space_size]>(base_field_scratch);
                let ext_field_scratch = core::mem::transmute::<_, &[[S::ExtFieldInput; 1]; #ext_field_scratch_space_size]>(ext_field_scratch);
                #quadratic_only_fn_id::<F, E, S, _>(
                    base_field_scratch,
                    ext_field_scratch,
                    sumcheck_challenges,
                    lookup_alpha_powers,
                    lookup_gamma,
                    base_repr_ctx,
                    ext_repr_ctx,
                    0
                )
            };

            [c0, c1]
        }
    };

    let compute_fn = quote! {
        #[inline(always)]
        pub fn #compute_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, const EXPLICIT_FORM: bool>(
            base_field_scratch: &[[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            ext_field_scratch: &[[S::ExtFieldInput; 2]; #ext_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            external_challenges: &impl GKRExternalChallengesProvider<F, E>,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
        ) -> [E; 2] {
            let c0 = #explicit_fn_id::<F, E, S>(
                base_field_scratch,
                ext_field_scratch,
                sumcheck_challenges,
                lookup_alpha_powers,
                lookup_gamma,
                base_repr_ctx,
                ext_repr_ctx,
                0,
            );

            let c1 = if EXPLICIT_FORM {
                #explicit_fn_id::<F, E, S>(
                    base_field_scratch,
                    ext_field_scratch,
                    sumcheck_challenges,
                    lookup_alpha_powers,
                    lookup_gamma,
                    base_repr_ctx,
                    ext_repr_ctx,
                    1,
                )
            } else {
                #quadratic_only_fn_id::<F, E, S, _>(
                    base_field_scratch,
                    ext_field_scratch,
                    sumcheck_challenges,
                    lookup_alpha_powers,
                    lookup_gamma,
                    base_repr_ctx,
                    ext_repr_ctx,
                    1,
                )
            };

            [c0, c1]
        }
    };

    (compute_fn_initial_round, compute_fn)
}
