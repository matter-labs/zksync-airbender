use super::*;
use cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation;

pub(crate) fn generate_compute_fns<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &[NoFieldSpecialMemoryContributionRelation; 2],
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

    let output_to_read = all_ext_outputs
        .iter()
        .position(|el| *el == output)
        .expect("pos");

    // we can generate quadratic part evaluation fn and plain evaluation fns

    let mut parts = [(quote! {}, quote! {}), (quote! {}, quote! {})];
    for (dst, rel) in parts.iter_mut().zip(input.iter()) {
        let mut quadratic_fn = quote! {
            let mut acc = E::ZERO;
        };

        let mut explicit_fn = quote! {
            let mut acc = *external_challenges.additive_part();
        };

        use cs::definitions::gkr::AddressSpaceType;
        use cs::definitions::*;
        use cs::gkr_compiler::*;

        match rel.address_space {
            CompiledAddressSpaceRelationStrict::Constant(c) => {
                assert!(c < (1u32 << 16));
                // doesn't contribute to quadratic part
                if c != 0 {
                    explicit_fn.extend(quote! {
                        acc.add_assign_base(&F::from_u32_unchecked(#c));
                    });
                }
            }
            CompiledAddressSpaceRelationStrict::IsRam(offset) => {
                // if "true", then we should have address space == RAM (1)
                assert_eq!(AddressSpaceType::RAM as u8, 1);
                let address = GKRAddress::BaseLayerMemory(offset);
                let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                explicit_fn.extend(
                    quote! {
                        acc = base_field_scratch[#input_scratch_to_use][subindex].add_with_ext(&acc, base_repr_ctx);
                    }
                );
                quadratic_fn.extend(
                    quote! {
                        acc = base_field_scratch[#input_scratch_to_use][subindex].add_with_ext(&acc, base_repr_ctx);
                    }
                );
            }
            CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
                // if "true", then we should have address space == register (0)
                assert_eq!(AddressSpaceType::Register as u8, 0);
                let address = GKRAddress::BaseLayerMemory(offset);
                let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                explicit_fn.extend(
                    quote! {
                        acc.add_assign_base(&F::ONE);
                        acc = base_field_scratch[#input_scratch_to_use][subindex].sub_from_ext(&acc, base_repr_ctx);
                    }
                );
                quadratic_fn.extend(
                    quote! {
                        acc = base_field_scratch[#input_scratch_to_use][subindex].sub_from_ext(&acc, base_repr_ctx);
                    }
                );
            }
        }
        match &rel.address {
            &CompiledAddressStrict::ConstantU16(c) => {
                if c != 0 {
                    explicit_fn.extend(quote! {
                        let mut t = external_challenges.linearization_challenges()
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        t.mul_assign_by_base(&F::from_u32_unchecked(#c as u32));
                        acc.add_assign(&t);
                    });
                }

            }
            &CompiledAddressStrict::Constant(c) => {
                assert!(c < (1u32 << 16));
                if c != 0 {
                    explicit_fn.extend(quote! {
                        let mut t = external_challenges.linearization_challenges()
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        t.mul_assign_by_base(&F::from_u32_unchecked(#c));
                        acc.add_assign(&t);
                    });
                }
            }
            &CompiledAddressStrict::U16Space(offset) => {
                let address = GKRAddress::BaseLayerMemory(offset);
                let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                explicit_fn.extend(
                    quote! {
                        let t = external_challenges.linearization_challenges()
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                        acc.add_assign(&t);
                    }
                );
                quadratic_fn.extend(
                    quote! {
                        let t = external_challenges.linearization_challenges()
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                        let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                        acc.add_assign(&t);
                    }
                );
            }
            &CompiledAddressStrict::U32Space([low, high]) => {
                for (idx, offset) in [
                    (
                        quote! { PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX },
                        low,
                    ),
                    (
                        quote! { PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX },
                        high,
                    ),
                ] {
                    let address = GKRAddress::BaseLayerMemory(offset);
                    let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                    explicit_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [#idx];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                    quadratic_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [#idx];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                }
            }
            CompiledAddressStrict::U32SpaceGeneric(..) => {
                todo!();
            }
            CompiledAddressStrict::U32SpaceSpecialIndirect {
                low_base,
                low_dynamic_offset,
                low_offset,
                high,
            } => {
                todo!();

                // let mut low_offset = *low_offset;
                // if let Some((c, offset)) = *low_dynamic_offset {
                //     let t = mem_access_fn(base_layer_memory_sources, offset, row).as_u32_reduced();
                //     low_offset += t.wrapping_mul(c as u32);
                // }
                // {
                //     let mut t = external_challenges.permutation_argument_linearization_challenges
                //         [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                //     let mut el = mem_access_fn(base_layer_memory_sources, *low_base, row);
                //     el.add_assign(&F::from_u32_unchecked(low_offset));
                //     t.mul_assign_by_base(&el);
                //     result.add_assign(&t);
                // }
                // {
                //     let mut t = external_challenges.permutation_argument_linearization_challenges
                //         [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                //     let el = mem_access_fn(base_layer_memory_sources, *high, row);
                //     t.mul_assign_by_base(&el);
                //     result.add_assign(&t);
                // }
            }
        }
        // timestamp is a little special as we do add constant offset

        match rel.timestamp {
            CompiledMemoryTimestamp::Zero => {}
            CompiledMemoryTimestamp::Normal(ts) => {
                {
                    let address = GKRAddress::BaseLayerMemory(ts[0]);
                    let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                    let timestamp_offset = rel.timestamp_offset;
                    explicit_fn.extend(quote! {
                        let t = external_challenges.linearization_challenges()
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        let val = base_field_scratch[#input_scratch_to_use][subindex];
                    });
                    if timestamp_offset != 0 {
                        explicit_fn.extend(quote! {
                            let val = val.add_base(&F::from_u32_unchecked(#timestamp_offset));
                        });
                    }
                    explicit_fn.extend(quote! {
                        let t = val.mul_by_ext(&t, base_repr_ctx);
                        acc.add_assign(&t);
                    });
                    
                    quadratic_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                }
                {
                    let address = GKRAddress::BaseLayerMemory(ts[1]);
                    let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                    explicit_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                    quadratic_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                }
            }
        }

        use cs::definitions::gkr::RamWordRepresentation;
        // and values are simplified for now
        match rel.value {
            RamWordRepresentation::Zero => {
                // nothing
            }
            RamWordRepresentation::U16Limbs(read_value) => {
                for (idx, offset) in [
                    (
                        quote! { PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX },
                        read_value[0],
                    ),
                    (
                        quote! { PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX },
                        read_value[1],
                    ),
                ] {
                    let address = GKRAddress::BaseLayerMemory(offset);
                    let input_scratch_to_use = pos_state.get(&address).expect("pos").cache_pos;
                    explicit_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [#idx];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                    quadratic_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [#idx];
                            let t = base_field_scratch[#input_scratch_to_use][subindex].mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                }
            }
            RamWordRepresentation::U8Limbs(read_value_bytes) => {
                explicit_fn.extend(quote! {
                    let byte_shift = F::from_u32_unchecked(1u32 << 8);
                });
                quadratic_fn.extend(quote! {
                    let byte_shift = F::from_u32_unchecked(1u32 << 8);
                });

                for (idx, offset_low, offset_high) in [
                    (
                        quote! { PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX },
                        read_value_bytes[0],
                        read_value_bytes[1],
                    ),
                    (
                        quote! { PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX },
                        read_value_bytes[2],
                        read_value_bytes[3],
                    ),
                ] {
                    let address_low = GKRAddress::BaseLayerMemory(offset_low);
                    let address_high = GKRAddress::BaseLayerMemory(offset_high);
                    let input_scratch_to_use_low =
                        pos_state.get(&address_low).expect("pos").cache_pos;
                    let input_scratch_to_use_high =
                        pos_state.get(&address_high).expect("pos").cache_pos;
                    explicit_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [#idx];
                            let val = base_field_scratch[#input_scratch_to_use_low][subindex].mul_by_ext(&t, base_repr_ctx);
                            let high = base_field_scratch[#input_scratch_to_use_high][subindex].mul_by_ext(&t, base_repr_ctx);
                            let high = high.mul_by_base(&byte_shift);
                            let val = val.add_other(&high);
                            let t = val.mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                    quadratic_fn.extend(
                        quote! {
                            let t = external_challenges.linearization_challenges()
                                [#idx];
                            let val = base_field_scratch[#input_scratch_to_use_low][subindex].mul_by_ext(&t, base_repr_ctx);
                            let high = base_field_scratch[#input_scratch_to_use_high][subindex].mul_by_ext(&t, base_repr_ctx);
                            let high = high.mul_by_base(&byte_shift);
                            let val = val.add_other(&high);
                            let t = val.mul_by_ext(&t, base_repr_ctx);
                            acc.add_assign(&t);
                        }
                    );
                }
            }
        }

        *dst = (quadratic_fn, explicit_fn);
    }

    let [(quad_0, expl_0), (quad_1, expl_1)] = parts;
    let explicit_inner = quote! {
        let mut acc = {
            #expl_0

            acc
        };

        let acc_1 = {
            #expl_1

            acc
        };
        acc.mul_assign(&acc_1);

        acc
    };

    let quad_inner = quote! {
        let mut acc = {
            #quad_0

            acc
        };

        let acc_1 = {
            #quad_1

            acc
        };
        acc.mul_assign(&acc_1);

        acc
    };

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
            external_challenges: &impl GKRExternalChallengesProvider<F, E>,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(N > 0);
                core::hint::assert_unchecked(subindex < N);
            }
            #quad_inner
        }
    };

    let explicit_fn = quote! {
        #[inline(always)]
        fn #explicit_fn_id<F: PrimeField, E: FieldExtension<F> + Field, S: SumcheckRoundSource<F, E>>(
            base_field_scratch: &[[S::BaseFieldInput; 2]; #base_field_scratch_space_size],
            external_challenges: &impl GKRExternalChallengesProvider<F, E>,
            base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
            subindex: usize
        ) -> E {
            unsafe {
                core::hint::assert_unchecked(subindex < 2);
            }
            #explicit_inner
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
            let c0 = all_ext_outputs[#output_to_read].get_f0_only::<false>(row_index).mul_by_ext(&sumcheck_challenges[#challenge_to_use], ext_repr_ctx);

            let mut c1 = unsafe {
                let base_field_scratch = core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; #base_field_scratch_space_size]>(base_field_scratch);
                #quadratic_only_fn_id::<F, E, S, _>(
                    base_field_scratch,
                    external_challenges,
                    base_repr_ctx,
                    0
                )
            };
            c1.mul_assign(&sumcheck_challenges[#challenge_to_use]);

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
            let mut c0 = #explicit_fn_id::<F, E, S>(
                base_field_scratch,
                external_challenges,
                base_repr_ctx,
                0,
            );
            c0.mul_assign(&sumcheck_challenges[#challenge_to_use]);

            let mut c1 = if EXPLICIT_FORM {
                #explicit_fn_id::<F, E, S>(
                    base_field_scratch,
                    external_challenges,
                    base_repr_ctx,
                    1,
                )
            } else {
                #quadratic_only_fn_id::<F, E, S, _>(
                    base_field_scratch,
                    external_challenges,
                    base_repr_ctx,
                    1,
                )
            };
            c1.mul_assign(&sumcheck_challenges[#challenge_to_use]);

            [c0, c1]
        }
    };

    (compute_fn_initial_round, compute_fn)
}
