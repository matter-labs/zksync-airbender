use super::*;
use cs::gkr_compiler::NoFieldStructuredExpression;

fn filter_out_for_degree_only(
    input: &NoFieldStructuredExpression,
    degree: usize,
) -> Option<NoFieldStructuredExpression> {
    assert!(degree > 0);
    if input.degree() < degree {
        return None;
    }

    match input {
        NoFieldStructuredExpression::Constant(..) => {
            assert!(degree > 0);
            if degree == 0 {
                Some(input.clone())
            } else {
                None
            }
        }
        NoFieldStructuredExpression::Place(..) => {
            assert!(degree > 0);
            if degree == 1 {
                Some(input.clone())
            } else {
                None
            }
        }
        NoFieldStructuredExpression::Sum(p) => {
            let filtered_sum: Vec<_> = p
                .iter()
                .filter_map(|el| {
                    if el.degree() < degree {
                        None
                    } else {
                        filter_out_for_degree_only(el, degree)
                    }
                })
                .collect();
            if filtered_sum.is_empty() {
                None
            } else {
                Some(NoFieldStructuredExpression::Sum(filtered_sum))
            }
        }
        NoFieldStructuredExpression::Product(p) => {
            let filtered_product: Vec<_> = p
                .iter()
                .filter_map(|el| {
                    if let NoFieldStructuredExpression::Constant(..) = el {
                        Some(el.clone())
                    } else {
                        filter_out_for_degree_only(el, 1)
                    }
                })
                .collect();
            if filtered_product.is_empty() {
                None
            } else {
                Some(NoFieldStructuredExpression::Product(filtered_product))
            }
        }
    }
}

fn get_ssa_ident(ssa_index: &mut usize) -> Ident {
    let ssa_idx_to_use = *ssa_index;
    *ssa_index += 1;
    Ident::new(&format!("ssa_{}", ssa_idx_to_use), Span::call_site())
}

fn transform_term(
    input: &NoFieldStructuredExpression,
    pos_state: &BTreeMap<GKRAddress, SumcheckAddressState>,
    ssa_index: &mut usize,
) -> (Ident, bool, TokenStream) {
    match input {
        NoFieldStructuredExpression::Constant(c) => {
            let out_ssa = get_ssa_ident(ssa_index);
            (
                out_ssa.clone(),
                false,
                quote! {
                    let #out_ssa = F::from_u32_unchecked(#c);
                },
            )

            // let ssa = get_ssa_ident(ssa_index);
            // let c = *c;
            // statement.extend(quote! {
            //     let #ssa = F::from_u32_unchecked(#c);
            // });
        }
        NoFieldStructuredExpression::Place(place) => {
            let input_scratch_to_use = pos_state.get(place).expect("pos").cache_pos;
            let out_ssa = get_ssa_ident(ssa_index);
            (
                out_ssa.clone(),
                false,
                quote! {
                    let #out_ssa = base_field_scratch[#input_scratch_to_use][subindex];
                },
            )
            // let ssa = get_ssa_ident(ssa_index);
            // let input_scratch_to_use = pos_state.get(place).expect("pos").cache_pos;
            // statement.extend(quote! {
            //     let #ssa = base_field_scratch[#input_scratch_to_use][subindex];
            // });
        }

        NoFieldStructuredExpression::Sum(terms) => {
            let mut statement = quote! {};

            // we want to sort by degree
            let deg_2: Vec<_> = terms
                .iter()
                .filter(|el| el.degree() == 2)
                .cloned()
                .collect();
            let deg_1: Vec<_> = terms
                .iter()
                .filter(|el| el.degree() == 1)
                .cloned()
                .collect();
            let constants: Vec<_> = terms
                .iter()
                .filter(|el| el.degree() == 0)
                .cloned()
                .collect();
            assert!(constants.len() <= 1);
            let mut previous_ssa: Option<Ident> = None;
            if deg_2.len() > 0 {
                for el in deg_2.into_iter() {
                    let (out_ssa, _, inner_stream) = transform_term(&el, pos_state, ssa_index);
                    if let Some(previous_ssa_to_use) = previous_ssa.take() {
                        let ssa = get_ssa_ident(ssa_index);
                        statement.extend(quote! {
                            #inner_stream
                            let #ssa = #previous_ssa_to_use.add_other(& #out_ssa);
                        });
                        previous_ssa = Some(ssa);
                    } else {
                        statement.extend(quote! {
                            #inner_stream
                        });
                        previous_ssa = Some(out_ssa);
                    }
                }

                for el in deg_1.into_iter() {
                    let (out_ssa, _, inner_stream) = transform_term(&el, pos_state, ssa_index);
                    if let Some(previous_ssa_to_use) = previous_ssa.take() {
                        let ssa = get_ssa_ident(ssa_index);
                        statement.extend(quote! {
                            #inner_stream
                            let #ssa = #previous_ssa_to_use.add_base_repr(& #out_ssa);
                        });
                        previous_ssa = Some(ssa);
                    } else {
                        unreachable!();
                    }
                }
            } else {
                assert!(deg_1.len() > 0);
                for el in deg_1.into_iter() {
                    let (out_ssa, _, inner_stream) = transform_term(&el, pos_state, ssa_index);
                    if let Some(previous_ssa_to_use) = previous_ssa.take() {
                        let ssa = get_ssa_ident(ssa_index);
                        statement.extend(quote! {
                            #inner_stream
                            let #ssa = #previous_ssa_to_use.add_other(& #out_ssa);
                        });
                        previous_ssa = Some(ssa);
                    } else {
                        statement.extend(quote! {
                            #inner_stream
                        });
                        previous_ssa = Some(out_ssa);
                    }
                }
            }
            if constants.len() > 0 {
                let NoFieldStructuredExpression::Constant(c) = constants[0].clone() else {
                    unreachable!()
                };
                if let Some(previous_ssa_to_use) = previous_ssa.take() {
                    let ssa = get_ssa_ident(ssa_index);
                    statement.extend(quote! {
                        let #ssa = #previous_ssa_to_use.add_base(& F::from_u32_unchecked(#c));
                    });
                    previous_ssa = Some(ssa);
                } else {
                    unreachable!()
                }
            }

            let previous_ssa_to_use = previous_ssa.unwrap();
            statement.extend(quote! {
                #previous_ssa_to_use
            });

            let out_ssa = get_ssa_ident(ssa_index);
            (
                out_ssa.clone(),
                false,
                quote! {
                    let #out_ssa = {
                        #statement
                    };
                },
            )
        }
        NoFieldStructuredExpression::Product(terms) => {
            let mut statement = quote! {};
            // we want to sort by degree
            let deg_2: Vec<_> = terms
                .iter()
                .filter(|el| el.degree() == 2)
                .cloned()
                .collect();
            let deg_1: Vec<_> = terms
                .iter()
                .filter(|el| el.degree() == 1)
                .cloned()
                .collect();
            let constants: Vec<_> = terms
                .iter()
                .filter(|el| el.degree() == 0)
                .cloned()
                .collect();
            assert!(constants.len() <= 1);
            let mut previous_ssa: Option<Ident> = None;
            if deg_2.len() > 0 {
                assert_eq!(deg_1.len(), 0);
                for el in deg_2.into_iter() {
                    let (out_ssa, _, inner_stream) = transform_term(&el, pos_state, ssa_index);
                    if let Some(previous_ssa_to_use) = previous_ssa.take() {
                        unreachable!();
                        // let ssa = get_ssa_ident(ssa_index);
                        // statement.extend(quote! {
                        //     #inner_stream
                        //     let #ssa = #previous_ssa_to_use.add_other(& #out_ssa);
                        // });
                        // previous_ssa = Some(ssa);
                    } else {
                        statement.extend(quote! {
                            #inner_stream
                        });
                        previous_ssa = Some(out_ssa);
                    }
                }
            } else {
                for el in deg_1.into_iter() {
                    let (out_ssa, _, inner_stream) = transform_term(&el, pos_state, ssa_index);
                    if let Some(previous_ssa_to_use) = previous_ssa.take() {
                        let ssa = get_ssa_ident(ssa_index);
                        statement.extend(quote! {
                            #inner_stream
                            let #ssa = #previous_ssa_to_use.mul_with_other(& #out_ssa);
                        });
                        previous_ssa = Some(ssa);
                    } else {
                        statement.extend(quote! {
                            #inner_stream
                        });
                        previous_ssa = Some(out_ssa);
                    }
                }
            }
            if constants.len() > 0 {
                let NoFieldStructuredExpression::Constant(c) = constants[0].clone() else {
                    unreachable!()
                };
                if let Some(previous_ssa_to_use) = previous_ssa.take() {
                    let ssa = get_ssa_ident(ssa_index);
                    statement.extend(quote! {
                        let #ssa = #previous_ssa_to_use.mul_by_base(& F::from_u32_unchecked(#c));
                    });
                    previous_ssa = Some(ssa);
                } else {
                    unreachable!()
                }
            }

            let previous_ssa_to_use = previous_ssa.unwrap();
            statement.extend(quote! {
                #previous_ssa_to_use
            });

            let out_ssa = get_ssa_ident(ssa_index);
            (
                out_ssa.clone(),
                false,
                quote! {
                    let #out_ssa = {
                        #statement
                    };
                },
            )
        }
    }
}

pub(crate) fn generate_compute_fns<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &NoFieldStructuredExpression,
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
    let mut filtered_for_quadratic_only = filter_out_for_degree_only(input, 2);

    let (compute_fn_initial_round_id, compute_fn_id) = compute_fn_ids(gate_idx, layer_idx);

    let num_base_field_outputs = all_base_outputs.len();
    let num_ext_field_outputs = all_ext_outputs.len();

    assert_eq!(challenges.len(), 1);
    let challenge_to_use = challenges[0];

    // we can generate quadratic part evaluation fn and plain evaluation fns

    let mut ssa_index = 0;
    let (explicit_ssa_final_ident, _, explicit_ssa_token_steam) =
        transform_term(input, pos_state, &mut ssa_index);

    let explicit_fn_id = Ident::new(
        &format!("compute_layer_{}_gate_{}_explicit", layer_idx, gate_idx),
        Span::call_site(),
    );

    if let Some(filtered_for_quadratic_only) = filtered_for_quadratic_only.take() {
        let mut ssa_index = 0;
        let (quadratic_ssa_final_ident, _, quadratic_ssa_token_steam) =
            transform_term(&filtered_for_quadratic_only, pos_state, &mut ssa_index);

        let quadratic_only_fn_id = Ident::new(
            &format!(
                "compute_layer_{}_gate_{}_quadratic_part_only",
                layer_idx, gate_idx
            ),
            Span::call_site(),
        );

        let quad_fn = quote! {
            #[inline(always)]
            fn #quadratic_only_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>, const N: usize>(
                base_field_scratch: &[[S::BaseFieldInput; N]; #base_field_scratch_space_size],
                sumcheck_challenges: &[E; #num_challenges],
                base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
                subindex: usize
            ) -> E {
                unsafe {
                    core::hint::assert_unchecked(N > 0);
                    core::hint::assert_unchecked(subindex < N);
                }
                #quadratic_ssa_token_steam
                let val = #quadratic_ssa_final_ident;
                val.mul_by_ext(&sumcheck_challenges[#challenge_to_use], base_repr_ctx)
            }
        };

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
                #explicit_ssa_token_steam
                let val = #explicit_ssa_final_ident;
                val.mul_by_ext(&sumcheck_challenges[#challenge_to_use], base_repr_ctx)
            }
        };

        let compute_fn_initial_round = quote! {
            #quad_fn

            #explicit_fn

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
                let c1 = unsafe {
                    let base_field_scratch = core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; #base_field_scratch_space_size]>(base_field_scratch);
                    #quadratic_only_fn_id::<F, E, S, _>(
                        base_field_scratch,
                        sumcheck_challenges,
                        base_repr_ctx,
                        0
                    )
                };

                [E::ZERO, c1]
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
                    #quadratic_only_fn_id::<F, E, S, _>(
                        base_field_scratch,
                        sumcheck_challenges,
                        base_repr_ctx,
                        1,
                    )
                };

                [c0, c1]
            }
        };

        (compute_fn_initial_round, compute_fn)
    } else {
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
                #explicit_ssa_token_steam
                let val = #explicit_ssa_final_ident;
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
                external_challenges: &impl GKRExternalChallengesProvider<F, E>,
                lookup_alpha_powers: &[E],
                lookup_gamma: &E,
                base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
                ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
                row_index: usize,
            ) -> [E; 2] {
                [E::ZERO, E::ZERO]
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
}
