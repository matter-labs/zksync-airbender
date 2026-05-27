use super::*;
use cs::definitions::gkr::NoFieldSingleColumnLookupRelation;

pub(crate) fn generate_compute_fns<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &NoFieldSingleColumnLookupRelation,
    output: GKRAddress,
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

    assert_eq!(challenges.len(), 1);
    let challenge_to_use = challenges[0];

    let output_to_read = all_base_outputs
        .iter()
        .position(|el| *el == output)
        .expect("pos");

    // we can generate quadratic part evaluation fn and plain evaluation fns

    assert!(input.input.linear_terms.len() > 0);
    let mut acc_fn = quote! {};
    {
        let (c, address) = input.input.linear_terms[0];
        let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
        assert!(c != 0);

        if c != 1 {
            acc_fn.extend(quote! {
                let mut acc = base_field_scratch[#input_scratch_to_use][subindex].mul_by_base(&F::from_u32_unchecked(#c));
            });
        } else {
            acc_fn.extend(quote! {
                let mut acc = base_field_scratch[#input_scratch_to_use][subindex];
            });
        }
    }
    for (c, address) in input.input.linear_terms[1..].iter().copied() {
        let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
        assert!(c != 0);
        let cc = F::from_u32_unchecked(c);

        if cc == F::ONE {
            acc_fn.extend(quote! {
                acc = acc.add_other(&base_field_scratch[#input_scratch_to_use][subindex]);
            });
        } else if cc == F::MINUS_ONE {
            acc_fn.extend(quote! {
                acc = acc.sub_other(&base_field_scratch[#input_scratch_to_use][subindex]);
            });
        } else {
            acc_fn.extend(quote! {
                acc = acc.add_other(&base_field_scratch[#input_scratch_to_use][subindex].mul_by_base(&F::from_u32_unchecked(#c)));
            });
        }
    }

    let constant_quote = if input.input.constant != 0 {
        let c = input.input.constant;
        quote! {
            acc.add_base(&F::from_u32_unchecked(#c));
        }
    } else {
        quote! {}
    };

    let explicit_fn_id = Ident::new(
        &format!("compute_layer_{}_gate_{}_explicit", layer_idx, gate_idx),
        Span::call_site(),
    );

    let explicit_fn = quote! {
        #[inline(always)]
        fn #explicit_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &[[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(subindex < 2);
            }
            let val = {
                #acc_fn
                #constant_quote
                acc
            };
            val.mul_by_ext(&sumcheck_challenges[#challenge_to_use], base_repr_ctx)
        }
    };

    let compute_fn_initial_round = quote! {
        #explicit_fn

        #[inline(always)]
        pub fn #compute_fn_initial_round_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &[S::BaseFieldInput; #base_field_scratch_space_size],
            ext_field_scratch: &[S::ExtFieldInput; #ext_field_scratch_space_size],
            all_base_outputs: &[S::BaseInputAccessor; #num_base_field_outputs],
            all_ext_outputs: &[S::ExtInputAccessor; #num_ext_field_outputs],
            sumcheck_challenges: &[E; #num_challenges],
            external_challenges: &GKRExternalChallenges<F, E>,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            row_index: usize,
        ) -> [E; 2] {
            let c0 = all_base_outputs[#output_to_read].get_f0_only::<false>(row_index).mul_by_ext(&sumcheck_challenges[#challenge_to_use], base_repr_ctx);

            [c0, E::ZERO]
        }
    };

    let compute_fn = quote! {
        #[inline(always)]
        pub fn #compute_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, const EXPLICIT_FORM: bool>(
            base_field_scratch: &[[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            ext_field_scratch: &[[S::ExtFieldInput; 2]; #ext_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            external_challenges: &GKRExternalChallenges<F, E>,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
        ) -> [E; 2] {
            let c0 = #explicit_fn_id::<F, E, S>(
                base_field_scratch,
                sumcheck_challenges,
                base_repr_ctx,
                0,
            );

            let c1 = if EXPLICIT_FORM {
                #explicit_fn_id::<F, E, S>(
                    base_field_scratch,
                    sumcheck_challenges,
                    base_repr_ctx,
                    1,
                )
            } else {
                E::ZERO
            };

            [c0, c1]
        }
    };

    (compute_fn_initial_round, compute_fn)
}
