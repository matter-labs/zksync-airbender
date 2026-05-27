use super::*;

pub(crate) fn generate_compute_fns<F: PrimeField, E: FieldExtension<F> + Field>(
    input: GKRAddress,
    setup: [GKRAddress; 2],
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

    // we can generate quadratic part evaluation fn and plain evaluation fns

    // 1/(a + gamma) + b/(c + gamma) -> ()
    let a = pos_state.get(&input).expect("pos").cache_pos;
    let b = pos_state.get(&setup[0]).expect("pos").cache_pos;
    let c = pos_state.get(&setup[1]).expect("pos").cache_pos;

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

    let quad_fn = quote! {
        #[inline(always)]
        fn #quadratic_only_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, const N: usize>(
            base_field_scratch: &[[S::BaseFieldInput; N]; #base_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(N > 0);
                core::hint::assert_unchecked(subindex < N);
            }
            // 1/(a + gamma) + b/(c + gamma) -> (a * b), (a * c)
            let a = base_field_scratch[#a][subindex];
            let b = base_field_scratch[#b][subindex];
            let c = base_field_scratch[#c][subindex];
            let mut result = a.mul_with_other(&b).mul_by_ext(&sumcheck_challenges[#num_term_challenge], base_repr_ctx);
            let t = a.mul_with_other(&c).mul_by_ext(&sumcheck_challenges[#den_term_challenge], base_repr_ctx);
            result.add_assign(&t);

            result
        }
    };

    let explicit_fn = quote! {
        #[inline(always)]
        fn #explicit_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &[[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            sumcheck_challenges: &[E; #num_challenges],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(subindex < 2);
            }
            // 1/(a + gamma) + b/(c + gamma) -> (c + gamma + (a + gamma) * b, ((a + gamma) * (c + gamma))
            let a = base_field_scratch[#a][subindex];
            let b = base_field_scratch[#b][subindex];
            let c = base_field_scratch[#c][subindex];
            let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
            let c_plus_gamma = c.add_with_ext(lookup_gamma, base_repr_ctx);
            let mut result = b.mul_by_ext(&a_plus_gamma, base_repr_ctx);
            result.add_assign(&c_plus_gamma);
            result.mul_assign(&sumcheck_challenges[#num_term_challenge]);
            let mut den = a_plus_gamma;
            den.mul_assign(&c_plus_gamma);
            den.mul_assign(&sumcheck_challenges[#den_term_challenge]);
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
            external_challenges: &GKRExternalChallenges<F, E>,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            row_index: usize,
        ) -> [E; 2] {
            let mut c0 = all_ext_outputs[#num_output_to_read].get_f0_only::<false>(row_index).mul_by_ext(&sumcheck_challenges[#num_term_challenge], ext_repr_ctx);
            c0.add_assign(&all_ext_outputs[#den_output_to_read].get_f0_only::<false>(row_index).mul_by_ext(&sumcheck_challenges[#den_term_challenge], ext_repr_ctx));

            let c1 = unsafe {
                let base_field_scratch = core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; #base_field_scratch_space_size]>(base_field_scratch);
                #quadratic_only_fn_id::<F, E, S, _>(
                    base_field_scratch,
                    sumcheck_challenges,
                    lookup_gamma,
                    base_repr_ctx,
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
            external_challenges: &GKRExternalChallenges<F, E>,
            lookup_alpha_powers: &[E],
            lookup_gamma: &E,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
        ) -> [E; 2] {
            let c0 = #explicit_fn_id::<F, E, S>(
                base_field_scratch,
                sumcheck_challenges,
                lookup_gamma,
                base_repr_ctx,
                0,
            );

            let c1 = if EXPLICIT_FORM {
                #explicit_fn_id::<F, E, S>(
                    base_field_scratch,
                    sumcheck_challenges,
                    lookup_gamma,
                    base_repr_ctx,
                    1,
                )
            } else {
                #quadratic_only_fn_id::<F, E, S, _>(
                    base_field_scratch,
                    sumcheck_challenges,
                    lookup_gamma,
                    base_repr_ctx,
                    1,
                )
            };

            [c0, c1]
        }
    };

    (compute_fn_initial_round, compute_fn)
}
