#[inline(always)]
pub fn fetch_layer_0_gate_0_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[39usize] = all_base_inputs[39usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_0_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_base_outputs[0usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[0usize], base_repr_ctx);
    [c0, E::ZERO]
}
#[inline(always)]
pub fn fetch_layer_0_gate_1_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[22usize] = all_base_inputs[22usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[23usize] = all_base_inputs[23usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[24usize] = all_base_inputs[24usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[25usize] = all_base_inputs[25usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[26usize] = all_base_inputs[26usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[27usize] = all_base_inputs[27usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[28usize] = all_base_inputs[28usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[29usize] = all_base_inputs[29usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[30usize] = all_base_inputs[30usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[31usize] = all_base_inputs[31usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_1_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = *external_challenges.additive_part();
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[22usize][subindex];
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[23usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = *external_challenges.additive_part();
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[27usize][subindex];
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[28usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[30usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
fn compute_layer_0_gate_1_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[22usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[23usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[27usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[28usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[30usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
pub fn compute_layer_0_gate_1_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_ext_outputs[0usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[1usize], ext_repr_ctx);
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_1_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            0,
        )
    };
    c1.mul_assign(&sumcheck_challenges[1usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_2_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[42usize] = all_base_inputs[42usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[43usize] = all_base_inputs[43usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_2_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = *external_challenges.additive_part();
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = *external_challenges.additive_part();
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(1u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[30usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
fn compute_layer_0_gate_2_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[30usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
pub fn compute_layer_0_gate_2_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_ext_outputs[1usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[2usize], ext_repr_ctx);
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_2_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            0,
        )
    };
    c1.mul_assign(&sumcheck_challenges[2usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_3_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[32usize] = all_base_inputs[32usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[33usize] = all_base_inputs[33usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[34usize] = all_base_inputs[34usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[35usize] = all_base_inputs[35usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[36usize] = all_base_inputs[36usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[40usize] = all_base_inputs[40usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[41usize] = all_base_inputs[41usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_3_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = *external_challenges.additive_part();
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[32usize][subindex];
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[33usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[34usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[35usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = *external_challenges.additive_part();
        acc.add_assign_base(&F::from_u32_unchecked(2u32));
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[40usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[41usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
fn compute_layer_0_gate_3_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[32usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[33usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[34usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[35usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[40usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[41usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
pub fn compute_layer_0_gate_3_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_ext_outputs[2usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[3usize], ext_repr_ctx);
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_3_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            0,
        )
    };
    c1.mul_assign(&sumcheck_challenges[3usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_4_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[37usize] = all_base_inputs[37usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[38usize] = all_base_inputs[38usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[44usize] = all_base_inputs[44usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[45usize] = all_base_inputs[45usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[46usize] = all_base_inputs[46usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[47usize] = all_base_inputs[47usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_4_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = *external_challenges.additive_part();
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(2u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[37usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[38usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = *external_challenges.additive_part();
        acc.add_assign_base(&F::from_u32_unchecked(2u32));
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[46usize][subindex];
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[47usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[44usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[45usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
fn compute_layer_0_gate_4_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[37usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[38usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[46usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[47usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[44usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.linearization_challenges()
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[45usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    acc.mul_assign(&acc_1);
    acc
}
#[inline(always)]
pub fn compute_layer_0_gate_4_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_ext_outputs[3usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[4usize], ext_repr_ctx);
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_4_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            0,
        )
    };
    c1.mul_assign(&sumcheck_challenges[4usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_5_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[11usize] = all_base_inputs[11usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[19usize] = all_base_inputs[19usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[48usize] = all_base_inputs[48usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_5_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = base_field_scratch[11usize][subindex];
    let b = base_field_scratch[19usize][subindex];
    let c = base_field_scratch[48usize][subindex];
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let c_plus_gamma = c.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = c_plus_gamma;
    result.sub_assign(&b.mul_by_ext(&a_plus_gamma, base_repr_ctx));
    result.mul_assign(&sumcheck_challenges[5usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&c_plus_gamma);
    den.mul_assign(&sumcheck_challenges[6usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_5_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = base_field_scratch[11usize][subindex];
    let b = base_field_scratch[19usize][subindex];
    let c = base_field_scratch[48usize][subindex];
    let num = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[5usize], base_repr_ctx);
    let den = a
        .mul_with_other(&c)
        .mul_by_ext(&sumcheck_challenges[6usize], base_repr_ctx);
    let mut result = den;
    result.sub_assign(&num);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_5_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[4usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[5usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[5usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[6usize], ext_repr_ctx),
    );
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_5_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_6_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[12usize] = all_base_inputs[12usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_6_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = {
        let mut acc = base_field_scratch[12usize][subindex];
        acc
    };
    let b = {
        let mut acc = base_field_scratch[37usize][subindex];
        acc
    };
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let b_plus_gamma = b.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = a_plus_gamma;
    result.add_assign(&b_plus_gamma);
    result.mul_assign(&sumcheck_challenges[7usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&b_plus_gamma);
    den.mul_assign(&sumcheck_challenges[8usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_6_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = {
        let mut acc = base_field_scratch[12usize][subindex];
        acc
    };
    let b = {
        let mut acc = base_field_scratch[37usize][subindex];
        acc
    };
    let result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[8usize], base_repr_ctx);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_6_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[6usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[7usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[7usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[8usize], ext_repr_ctx),
    );
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_6_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_7_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_7_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = {
        let mut acc = base_field_scratch[38usize][subindex];
        acc
    };
    let b = {
        let mut acc = base_field_scratch[44usize][subindex];
        acc
    };
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let b_plus_gamma = b.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = a_plus_gamma;
    result.add_assign(&b_plus_gamma);
    result.mul_assign(&sumcheck_challenges[9usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&b_plus_gamma);
    den.mul_assign(&sumcheck_challenges[10usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_7_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = {
        let mut acc = base_field_scratch[38usize][subindex];
        acc
    };
    let b = {
        let mut acc = base_field_scratch[44usize][subindex];
        acc
    };
    let result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[10usize], base_repr_ctx);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_7_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[8usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[9usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[9usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[10usize], ext_repr_ctx),
    );
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_7_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_8_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_8_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_base_outputs[1usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[11usize], base_repr_ctx);
    [c0, E::ZERO]
}
#[inline(always)]
pub fn fetch_layer_0_gate_9_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[20usize] = all_base_inputs[20usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[49usize] = all_base_inputs[49usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_9_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = base_field_scratch[46usize][subindex];
    let b = base_field_scratch[20usize][subindex];
    let c = base_field_scratch[49usize][subindex];
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let c_plus_gamma = c.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = c_plus_gamma;
    result.sub_assign(&b.mul_by_ext(&a_plus_gamma, base_repr_ctx));
    result.mul_assign(&sumcheck_challenges[12usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&c_plus_gamma);
    den.mul_assign(&sumcheck_challenges[13usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_9_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = base_field_scratch[46usize][subindex];
    let b = base_field_scratch[20usize][subindex];
    let c = base_field_scratch[49usize][subindex];
    let num = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[12usize], base_repr_ctx);
    let den = a
        .mul_with_other(&c)
        .mul_by_ext(&sumcheck_challenges[13usize], base_repr_ctx);
    let mut result = den;
    result.sub_assign(&num);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_9_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[10usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[12usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[11usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[13usize], ext_repr_ctx),
    );
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_9_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_10_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[16usize] = all_base_inputs[16usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_10_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = {
        let mut acc = base_field_scratch[47usize][subindex];
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[22usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[16usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc
    };
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let b_plus_gamma = b.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = a_plus_gamma;
    result.add_assign(&b_plus_gamma);
    result.mul_assign(&sumcheck_challenges[14usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&b_plus_gamma);
    den.mul_assign(&sumcheck_challenges[15usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_10_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = {
        let mut acc = base_field_scratch[47usize][subindex];
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[22usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[16usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc
    };
    let result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[15usize], base_repr_ctx);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_10_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[12usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[14usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[13usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[15usize], ext_repr_ctx),
    );
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_10_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_11_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[17usize] = all_base_inputs[17usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_11_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = {
        let mut acc = base_field_scratch[43usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[23usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[16usize][subindex]);
        acc = acc.add_base(&F::from_u32_unchecked(524288u32));
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[27usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[17usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc = acc.add_base(&F::from_u32_unchecked(2013265920u32));
        acc
    };
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let b_plus_gamma = b.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = a_plus_gamma;
    result.add_assign(&b_plus_gamma);
    result.mul_assign(&sumcheck_challenges[16usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&b_plus_gamma);
    den.mul_assign(&sumcheck_challenges[17usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_11_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = {
        let mut acc = base_field_scratch[43usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[23usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[16usize][subindex]);
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[27usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[17usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc
    };
    let result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[17usize], base_repr_ctx);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_11_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[14usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[16usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[15usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[17usize], ext_repr_ctx),
    );
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_11_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_12_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[18usize] = all_base_inputs[18usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_12_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let a = {
        let mut acc = base_field_scratch[43usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[28usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[17usize][subindex]);
        acc = acc.add_base(&F::from_u32_unchecked(524288u32));
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[32usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[18usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc = acc.add_base(&F::from_u32_unchecked(2013265919u32));
        acc
    };
    let a_plus_gamma = a.add_with_ext(lookup_gamma, base_repr_ctx);
    let b_plus_gamma = b.add_with_ext(lookup_gamma, base_repr_ctx);
    let mut result = a_plus_gamma;
    result.add_assign(&b_plus_gamma);
    result.mul_assign(&sumcheck_challenges[18usize]);
    let mut den = a_plus_gamma;
    den.mul_assign(&b_plus_gamma);
    den.mul_assign(&sumcheck_challenges[19usize]);
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_12_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let a = {
        let mut acc = base_field_scratch[43usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[28usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[17usize][subindex]);
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex];
        acc = acc.negate();
        acc = acc.add_other(&base_field_scratch[32usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[18usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc
    };
    let result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[19usize], base_repr_ctx);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_12_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[16usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[18usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[17usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[19usize], ext_repr_ctx),
    );
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_12_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_13_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_13_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let val = {
        let mut acc = base_field_scratch[43usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[33usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[18usize][subindex]);
        acc = acc.add_base(&F::from_u32_unchecked(524288u32));
        acc
    };
    val.mul_by_ext(&sumcheck_challenges[20usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_13_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c0 = all_base_outputs[2usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[20usize], base_repr_ctx);
    [c0, E::ZERO]
}
#[inline(always)]
pub fn fetch_layer_0_gate_14_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[0usize] = all_base_inputs[0usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[1usize] = all_base_inputs[1usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[2usize] = all_base_inputs[2usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[3usize] = all_base_inputs[3usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[4usize] = all_base_inputs[4usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[5usize] = all_base_inputs[5usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[6usize] = all_base_inputs[6usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[7usize] = all_base_inputs[7usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[8usize] = all_base_inputs[8usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[9usize] = all_base_inputs[9usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[10usize] = all_base_inputs[10usize].get_f1_minus_f0_only::<false>(row_index);
    base_field_scratch[21usize] = all_base_inputs[21usize].get_f1_minus_f0_only::<false>(row_index);
    ext_field_scratch[0usize] = all_ext_inputs[0usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_14_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let input: E = {
        let mut acc = E::ZERO;
        let mut t = base_field_scratch[40usize][subindex];
        acc = t.add_with_ext(&acc, base_repr_ctx);
        let mut t = base_field_scratch[41usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[0usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[26usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[1usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[31usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[2usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[36usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[3usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[0usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[4usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[1usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[5usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[2usize][subindex];
        t = t.add_other(
            &base_field_scratch[3usize][subindex].mul_by_base(&F::from_u32_unchecked(2u32)),
        );
        t = t.add_other(
            &base_field_scratch[4usize][subindex].mul_by_base(&F::from_u32_unchecked(4u32)),
        );
        t = t.add_other(
            &base_field_scratch[5usize][subindex].mul_by_base(&F::from_u32_unchecked(8u32)),
        );
        t = t.add_other(
            &base_field_scratch[6usize][subindex].mul_by_base(&F::from_u32_unchecked(16u32)),
        );
        t = t.add_other(
            &base_field_scratch[7usize][subindex].mul_by_base(&F::from_u32_unchecked(32u32)),
        );
        t = t.add_other(
            &base_field_scratch[8usize][subindex].mul_by_base(&F::from_u32_unchecked(64u32)),
        );
        t = t.add_other(
            &base_field_scratch[9usize][subindex].mul_by_base(&F::from_u32_unchecked(128u32)),
        );
        t = t.add_other(
            &base_field_scratch[10usize][subindex].mul_by_base(&F::from_u32_unchecked(256u32)),
        );
        let t = t.mul_by_ext(&lookup_alpha_powers[6usize], base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mask = base_field_scratch[39usize][subindex];
    let multiplicity = base_field_scratch[21usize][subindex];
    let cached_setup = ext_field_scratch[0usize][subindex];
    let mut input_plus_gamma = input;
    input_plus_gamma.add_assign(lookup_gamma);
    let cached_setup_plus_gamma = cached_setup.add_with_ext(lookup_gamma, ext_repr_ctx);
    let mut num = mask.mul_by_ext(&cached_setup_plus_gamma, base_repr_ctx);
    let t = multiplicity.mul_by_ext(&input_plus_gamma, base_repr_ctx);
    num.sub_assign(&t);
    num.mul_assign(&sumcheck_challenges[21usize]);
    let mut den = input_plus_gamma;
    den.mul_assign(&cached_setup_plus_gamma);
    den.mul_assign(&sumcheck_challenges[22usize]);
    let mut result = num;
    result.add_assign(&den);
    result
}
#[inline(always)]
fn compute_layer_0_gate_14_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; N]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    lookup_alpha_powers: &[E],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let input: E = {
        let mut acc = E::ZERO;
        let mut t = base_field_scratch[40usize][subindex];
        acc = t.add_with_ext(&acc, base_repr_ctx);
        let mut t = base_field_scratch[41usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[0usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[26usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[1usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[31usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[2usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[36usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[3usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[0usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[4usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[1usize][subindex];
        let t = t.mul_by_ext(&lookup_alpha_powers[5usize], base_repr_ctx);
        acc.add_assign(&t);
        let mut t = base_field_scratch[2usize][subindex];
        t = t.add_other(
            &base_field_scratch[3usize][subindex].mul_by_base(&F::from_u32_unchecked(2u32)),
        );
        t = t.add_other(
            &base_field_scratch[4usize][subindex].mul_by_base(&F::from_u32_unchecked(4u32)),
        );
        t = t.add_other(
            &base_field_scratch[5usize][subindex].mul_by_base(&F::from_u32_unchecked(8u32)),
        );
        t = t.add_other(
            &base_field_scratch[6usize][subindex].mul_by_base(&F::from_u32_unchecked(16u32)),
        );
        t = t.add_other(
            &base_field_scratch[7usize][subindex].mul_by_base(&F::from_u32_unchecked(32u32)),
        );
        t = t.add_other(
            &base_field_scratch[8usize][subindex].mul_by_base(&F::from_u32_unchecked(64u32)),
        );
        t = t.add_other(
            &base_field_scratch[9usize][subindex].mul_by_base(&F::from_u32_unchecked(128u32)),
        );
        t = t.add_other(
            &base_field_scratch[10usize][subindex].mul_by_base(&F::from_u32_unchecked(256u32)),
        );
        let t = t.mul_by_ext(&lookup_alpha_powers[6usize], base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mask = base_field_scratch[39usize][subindex];
    let multiplicity = base_field_scratch[21usize][subindex];
    let cached_setup = ext_field_scratch[0usize][subindex];
    let mut num = cached_setup.mul_by_ext(&sumcheck_challenges[21usize], ext_repr_ctx);
    num = mask.mul_by_ext(&num, base_repr_ctx);
    let mut t = multiplicity.mul_by_ext(&input, base_repr_ctx);
    t.mul_assign(&sumcheck_challenges[21usize]);
    num.sub_assign(&t);
    let mut den = cached_setup.mul_by_ext(&sumcheck_challenges[22usize], ext_repr_ctx);
    den.mul_assign(&input);
    let mut result = num;
    result.add_assign(&den);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_14_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut c0 = all_ext_outputs[18usize]
        .get_f0_only::<false>(row_index)
        .mul_by_ext(&sumcheck_challenges[21usize], ext_repr_ctx);
    c0.add_assign(
        &all_ext_outputs[19usize]
            .get_f0_only::<false>(row_index)
            .mul_by_ext(&sumcheck_challenges[22usize], ext_repr_ctx),
    );
    let mut c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        let ext_field_scratch =
            core::mem::transmute::<_, &[[S::ExtFieldInput; 1]; 1usize]>(ext_field_scratch);
        compute_layer_0_gate_14_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            ext_field_scratch,
            sumcheck_challenges,
            lookup_alpha_powers,
            base_repr_ctx,
            ext_repr_ctx,
            0,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_15_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_15_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[39usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[39usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[23usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_15_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[39usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[39usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[23usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_15_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_15_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_16_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[15usize] = all_base_inputs[15usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_16_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_24 = {
        let ssa_8 = {
            let ssa_0 = base_field_scratch[8usize][subindex];
            let ssa_6 = {
                let ssa_1 = base_field_scratch[34usize][subindex];
                let ssa_4 = {
                    let ssa_2 = base_field_scratch[35usize][subindex];
                    let ssa_3 = ssa_2.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_3
                };
                let ssa_5 = ssa_1.add_other(&ssa_4);
                ssa_5
            };
            let ssa_7 = ssa_0.mul_with_other(&ssa_6);
            ssa_7
        };
        let ssa_22 = {
            let ssa_14 = {
                let ssa_9 = base_field_scratch[24usize][subindex];
                let ssa_12 = {
                    let ssa_10 = base_field_scratch[25usize][subindex];
                    let ssa_11 = ssa_10.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_11
                };
                let ssa_13 = ssa_9.add_other(&ssa_12);
                ssa_13
            };
            let ssa_20 = {
                let ssa_15 = base_field_scratch[29usize][subindex];
                let ssa_18 = {
                    let ssa_16 = base_field_scratch[30usize][subindex];
                    let ssa_17 = ssa_16.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_17
                };
                let ssa_19 = ssa_15.add_other(&ssa_18);
                ssa_19
            };
            let ssa_21 = ssa_14.mul_with_other(&ssa_20);
            ssa_21
        };
        let ssa_23 = ssa_8.add_other(&ssa_22);
        ssa_23
    };
    let val = ssa_24;
    val.mul_by_ext(&sumcheck_challenges[24usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_16_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_28 = {
        let ssa_8 = {
            let ssa_0 = base_field_scratch[8usize][subindex];
            let ssa_6 = {
                let ssa_1 = base_field_scratch[34usize][subindex];
                let ssa_4 = {
                    let ssa_2 = base_field_scratch[35usize][subindex];
                    let ssa_3 = ssa_2.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_3
                };
                let ssa_5 = ssa_1.add_other(&ssa_4);
                ssa_5
            };
            let ssa_7 = ssa_0.mul_with_other(&ssa_6);
            ssa_7
        };
        let ssa_22 = {
            let ssa_14 = {
                let ssa_9 = base_field_scratch[24usize][subindex];
                let ssa_12 = {
                    let ssa_10 = base_field_scratch[25usize][subindex];
                    let ssa_11 = ssa_10.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_11
                };
                let ssa_13 = ssa_9.add_other(&ssa_12);
                ssa_13
            };
            let ssa_20 = {
                let ssa_15 = base_field_scratch[29usize][subindex];
                let ssa_18 = {
                    let ssa_16 = base_field_scratch[30usize][subindex];
                    let ssa_17 = ssa_16.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_17
                };
                let ssa_19 = ssa_15.add_other(&ssa_18);
                ssa_19
            };
            let ssa_21 = ssa_14.mul_with_other(&ssa_20);
            ssa_21
        };
        let ssa_23 = ssa_8.add_other(&ssa_22);
        let ssa_26 = {
            let ssa_24 = base_field_scratch[15usize][subindex];
            let ssa_25 = ssa_24.mul_by_base(&F::from_u32_unchecked(2013265920u32));
            ssa_25
        };
        let ssa_27 = ssa_23.add_base_repr(&ssa_26);
        ssa_27
    };
    let val = ssa_28;
    val.mul_by_ext(&sumcheck_challenges[24usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_16_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_16_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_17_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_17_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_69 = {
        let ssa_15 = {
            let ssa_9 = {
                let ssa_0 = base_field_scratch[37usize][subindex];
                let ssa_3 = {
                    let ssa_1 = base_field_scratch[15usize][subindex];
                    let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_2
                };
                let ssa_4 = ssa_0.add_other(&ssa_3);
                let ssa_7 = {
                    let ssa_5 = base_field_scratch[38usize][subindex];
                    let ssa_6 = ssa_5.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_6
                };
                let ssa_8 = ssa_4.add_other(&ssa_7);
                ssa_8
            };
            let ssa_13 = {
                let ssa_10 = base_field_scratch[7usize][subindex];
                let ssa_11 = base_field_scratch[8usize][subindex];
                let ssa_12 = ssa_10.add_other(&ssa_11);
                ssa_12
            };
            let ssa_14 = ssa_9.mul_with_other(&ssa_13);
            ssa_14
        };
        let ssa_42 = {
            let ssa_16 = base_field_scratch[6usize][subindex];
            let ssa_40 = {
                let ssa_17 = base_field_scratch[37usize][subindex];
                let ssa_34 = {
                    let ssa_32 = {
                        let ssa_18 = base_field_scratch[24usize][subindex];
                        let ssa_26 = {
                            let ssa_24 = {
                                let ssa_19 = base_field_scratch[29usize][subindex];
                                let ssa_22 = {
                                    let ssa_20 = base_field_scratch[30usize][subindex];
                                    let ssa_21 =
                                        ssa_20.mul_by_base(&F::from_u32_unchecked(65536u32));
                                    ssa_21
                                };
                                let ssa_23 = ssa_19.add_other(&ssa_22);
                                ssa_23
                            };
                            let ssa_25 = ssa_24.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                            ssa_25
                        };
                        let ssa_27 = ssa_18.add_other(&ssa_26);
                        let ssa_30 = {
                            let ssa_28 = base_field_scratch[25usize][subindex];
                            let ssa_29 = ssa_28.mul_by_base(&F::from_u32_unchecked(65536u32));
                            ssa_29
                        };
                        let ssa_31 = ssa_27.add_other(&ssa_30);
                        ssa_31
                    };
                    let ssa_33 = ssa_32.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_33
                };
                let ssa_35 = ssa_17.add_other(&ssa_34);
                let ssa_38 = {
                    let ssa_36 = base_field_scratch[38usize][subindex];
                    let ssa_37 = ssa_36.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_37
                };
                let ssa_39 = ssa_35.add_other(&ssa_38);
                ssa_39
            };
            let ssa_41 = ssa_16.mul_with_other(&ssa_40);
            ssa_41
        };
        let ssa_43 = ssa_15.add_other(&ssa_42);
        let ssa_67 = {
            let ssa_44 = base_field_scratch[5usize][subindex];
            let ssa_65 = {
                let ssa_45 = base_field_scratch[37usize][subindex];
                let ssa_59 = {
                    let ssa_57 = {
                        let ssa_46 = base_field_scratch[24usize][subindex];
                        let ssa_47 = base_field_scratch[29usize][subindex];
                        let ssa_48 = ssa_46.add_other(&ssa_47);
                        let ssa_51 = {
                            let ssa_49 = base_field_scratch[30usize][subindex];
                            let ssa_50 = ssa_49.mul_by_base(&F::from_u32_unchecked(65536u32));
                            ssa_50
                        };
                        let ssa_52 = ssa_48.add_other(&ssa_51);
                        let ssa_55 = {
                            let ssa_53 = base_field_scratch[25usize][subindex];
                            let ssa_54 = ssa_53.mul_by_base(&F::from_u32_unchecked(65536u32));
                            ssa_54
                        };
                        let ssa_56 = ssa_52.add_other(&ssa_55);
                        ssa_56
                    };
                    let ssa_58 = ssa_57.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_58
                };
                let ssa_60 = ssa_45.add_other(&ssa_59);
                let ssa_63 = {
                    let ssa_61 = base_field_scratch[38usize][subindex];
                    let ssa_62 = ssa_61.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_62
                };
                let ssa_64 = ssa_60.add_other(&ssa_63);
                ssa_64
            };
            let ssa_66 = ssa_44.mul_with_other(&ssa_65);
            ssa_66
        };
        let ssa_68 = ssa_43.add_other(&ssa_67);
        ssa_68
    };
    let val = ssa_69;
    val.mul_by_ext(&sumcheck_challenges[25usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_17_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_69 = {
        let ssa_15 = {
            let ssa_9 = {
                let ssa_0 = base_field_scratch[37usize][subindex];
                let ssa_3 = {
                    let ssa_1 = base_field_scratch[15usize][subindex];
                    let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_2
                };
                let ssa_4 = ssa_0.add_other(&ssa_3);
                let ssa_7 = {
                    let ssa_5 = base_field_scratch[38usize][subindex];
                    let ssa_6 = ssa_5.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_6
                };
                let ssa_8 = ssa_4.add_other(&ssa_7);
                ssa_8
            };
            let ssa_13 = {
                let ssa_10 = base_field_scratch[7usize][subindex];
                let ssa_11 = base_field_scratch[8usize][subindex];
                let ssa_12 = ssa_10.add_other(&ssa_11);
                ssa_12
            };
            let ssa_14 = ssa_9.mul_with_other(&ssa_13);
            ssa_14
        };
        let ssa_42 = {
            let ssa_16 = base_field_scratch[6usize][subindex];
            let ssa_40 = {
                let ssa_17 = base_field_scratch[37usize][subindex];
                let ssa_34 = {
                    let ssa_32 = {
                        let ssa_18 = base_field_scratch[24usize][subindex];
                        let ssa_26 = {
                            let ssa_24 = {
                                let ssa_19 = base_field_scratch[29usize][subindex];
                                let ssa_22 = {
                                    let ssa_20 = base_field_scratch[30usize][subindex];
                                    let ssa_21 =
                                        ssa_20.mul_by_base(&F::from_u32_unchecked(65536u32));
                                    ssa_21
                                };
                                let ssa_23 = ssa_19.add_other(&ssa_22);
                                ssa_23
                            };
                            let ssa_25 = ssa_24.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                            ssa_25
                        };
                        let ssa_27 = ssa_18.add_other(&ssa_26);
                        let ssa_30 = {
                            let ssa_28 = base_field_scratch[25usize][subindex];
                            let ssa_29 = ssa_28.mul_by_base(&F::from_u32_unchecked(65536u32));
                            ssa_29
                        };
                        let ssa_31 = ssa_27.add_other(&ssa_30);
                        ssa_31
                    };
                    let ssa_33 = ssa_32.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_33
                };
                let ssa_35 = ssa_17.add_other(&ssa_34);
                let ssa_38 = {
                    let ssa_36 = base_field_scratch[38usize][subindex];
                    let ssa_37 = ssa_36.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_37
                };
                let ssa_39 = ssa_35.add_other(&ssa_38);
                ssa_39
            };
            let ssa_41 = ssa_16.mul_with_other(&ssa_40);
            ssa_41
        };
        let ssa_43 = ssa_15.add_other(&ssa_42);
        let ssa_67 = {
            let ssa_44 = base_field_scratch[5usize][subindex];
            let ssa_65 = {
                let ssa_45 = base_field_scratch[37usize][subindex];
                let ssa_59 = {
                    let ssa_57 = {
                        let ssa_46 = base_field_scratch[24usize][subindex];
                        let ssa_47 = base_field_scratch[29usize][subindex];
                        let ssa_48 = ssa_46.add_other(&ssa_47);
                        let ssa_51 = {
                            let ssa_49 = base_field_scratch[30usize][subindex];
                            let ssa_50 = ssa_49.mul_by_base(&F::from_u32_unchecked(65536u32));
                            ssa_50
                        };
                        let ssa_52 = ssa_48.add_other(&ssa_51);
                        let ssa_55 = {
                            let ssa_53 = base_field_scratch[25usize][subindex];
                            let ssa_54 = ssa_53.mul_by_base(&F::from_u32_unchecked(65536u32));
                            ssa_54
                        };
                        let ssa_56 = ssa_52.add_other(&ssa_55);
                        ssa_56
                    };
                    let ssa_58 = ssa_57.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_58
                };
                let ssa_60 = ssa_45.add_other(&ssa_59);
                let ssa_63 = {
                    let ssa_61 = base_field_scratch[38usize][subindex];
                    let ssa_62 = ssa_61.mul_by_base(&F::from_u32_unchecked(65536u32));
                    ssa_62
                };
                let ssa_64 = ssa_60.add_other(&ssa_63);
                ssa_64
            };
            let ssa_66 = ssa_44.mul_with_other(&ssa_65);
            ssa_66
        };
        let ssa_68 = ssa_43.add_other(&ssa_67);
        ssa_68
    };
    let val = ssa_69;
    val.mul_by_ext(&sumcheck_challenges[25usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_17_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_17_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_18_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[14usize] = all_base_inputs[14usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_18_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_11 = {
        let ssa_3 = {
            let ssa_2 = {
                let ssa_0 = base_field_scratch[14usize][subindex];
                let ssa_1 = ssa_0.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                ssa_1
            };
            ssa_2
        };
        let ssa_9 = {
            let ssa_4 = base_field_scratch[5usize][subindex];
            let ssa_5 = base_field_scratch[6usize][subindex];
            let ssa_6 = ssa_4.add_other(&ssa_5);
            let ssa_7 = base_field_scratch[7usize][subindex];
            let ssa_8 = ssa_6.add_other(&ssa_7);
            ssa_8
        };
        let ssa_10 = ssa_3.mul_with_other(&ssa_9);
        ssa_10
    };
    let val = ssa_11;
    val.mul_by_ext(&sumcheck_challenges[26usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_18_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_12 = {
        let ssa_4 = {
            let ssa_2 = {
                let ssa_0 = base_field_scratch[14usize][subindex];
                let ssa_1 = ssa_0.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                ssa_1
            };
            let ssa_3 = ssa_2.add_base(&F::from_u32_unchecked(1u32));
            ssa_3
        };
        let ssa_10 = {
            let ssa_5 = base_field_scratch[5usize][subindex];
            let ssa_6 = base_field_scratch[6usize][subindex];
            let ssa_7 = ssa_5.add_other(&ssa_6);
            let ssa_8 = base_field_scratch[7usize][subindex];
            let ssa_9 = ssa_7.add_other(&ssa_8);
            ssa_9
        };
        let ssa_11 = ssa_4.mul_with_other(&ssa_10);
        ssa_11
    };
    let val = ssa_12;
    val.mul_by_ext(&sumcheck_challenges[26usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_18_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_18_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_19_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[13usize] = all_base_inputs[13usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
fn compute_layer_0_gate_19_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_68 = {
        let ssa_17 = {
            let ssa_9 = {
                let ssa_0 = base_field_scratch[11usize][subindex];
                let ssa_3 = {
                    let ssa_1 = base_field_scratch[13usize][subindex];
                    let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_2
                };
                let ssa_4 = ssa_0.add_other(&ssa_3);
                let ssa_7 = {
                    let ssa_5 = base_field_scratch[37usize][subindex];
                    let ssa_6 = ssa_5.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_6
                };
                let ssa_8 = ssa_4.add_other(&ssa_7);
                ssa_8
            };
            let ssa_15 = {
                let ssa_10 = base_field_scratch[5usize][subindex];
                let ssa_11 = base_field_scratch[6usize][subindex];
                let ssa_12 = ssa_10.add_other(&ssa_11);
                let ssa_13 = base_field_scratch[7usize][subindex];
                let ssa_14 = ssa_12.add_other(&ssa_13);
                ssa_14
            };
            let ssa_16 = ssa_9.mul_with_other(&ssa_15);
            ssa_16
        };
        let ssa_32 = {
            let ssa_18 = base_field_scratch[3usize][subindex];
            let ssa_30 = {
                let ssa_19 = base_field_scratch[29usize][subindex];
                let ssa_20 = base_field_scratch[37usize][subindex];
                let ssa_21 = ssa_19.add_other(&ssa_20);
                let ssa_24 = {
                    let ssa_22 = base_field_scratch[13usize][subindex];
                    let ssa_23 = ssa_22.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_23
                };
                let ssa_25 = ssa_21.add_other(&ssa_24);
                let ssa_28 = {
                    let ssa_26 = base_field_scratch[24usize][subindex];
                    let ssa_27 = ssa_26.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_27
                };
                let ssa_29 = ssa_25.add_other(&ssa_28);
                ssa_29
            };
            let ssa_31 = ssa_18.mul_with_other(&ssa_30);
            ssa_31
        };
        let ssa_33 = ssa_17.add_other(&ssa_32);
        let ssa_48 = {
            let ssa_34 = base_field_scratch[4usize][subindex];
            let ssa_46 = {
                let ssa_35 = base_field_scratch[0usize][subindex];
                let ssa_36 = base_field_scratch[40usize][subindex];
                let ssa_37 = ssa_35.add_other(&ssa_36);
                let ssa_40 = {
                    let ssa_38 = base_field_scratch[13usize][subindex];
                    let ssa_39 = ssa_38.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_39
                };
                let ssa_41 = ssa_37.add_other(&ssa_40);
                let ssa_44 = {
                    let ssa_42 = base_field_scratch[37usize][subindex];
                    let ssa_43 = ssa_42.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_43
                };
                let ssa_45 = ssa_41.add_other(&ssa_44);
                ssa_45
            };
            let ssa_47 = ssa_34.mul_with_other(&ssa_46);
            ssa_47
        };
        let ssa_49 = ssa_33.add_other(&ssa_48);
        let ssa_66 = {
            let ssa_50 = base_field_scratch[2usize][subindex];
            let ssa_64 = {
                let ssa_51 = base_field_scratch[0usize][subindex];
                let ssa_52 = base_field_scratch[24usize][subindex];
                let ssa_53 = ssa_51.add_other(&ssa_52);
                let ssa_54 = base_field_scratch[29usize][subindex];
                let ssa_55 = ssa_53.add_other(&ssa_54);
                let ssa_58 = {
                    let ssa_56 = base_field_scratch[13usize][subindex];
                    let ssa_57 = ssa_56.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_57
                };
                let ssa_59 = ssa_55.add_other(&ssa_58);
                let ssa_62 = {
                    let ssa_60 = base_field_scratch[37usize][subindex];
                    let ssa_61 = ssa_60.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_61
                };
                let ssa_63 = ssa_59.add_other(&ssa_62);
                ssa_63
            };
            let ssa_65 = ssa_50.mul_with_other(&ssa_64);
            ssa_65
        };
        let ssa_67 = ssa_49.add_other(&ssa_66);
        ssa_67
    };
    let val = ssa_68;
    val.mul_by_ext(&sumcheck_challenges[27usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_19_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_69 = {
        let ssa_18 = {
            let ssa_10 = {
                let ssa_0 = base_field_scratch[11usize][subindex];
                let ssa_3 = {
                    let ssa_1 = base_field_scratch[13usize][subindex];
                    let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_2
                };
                let ssa_4 = ssa_0.add_other(&ssa_3);
                let ssa_7 = {
                    let ssa_5 = base_field_scratch[37usize][subindex];
                    let ssa_6 = ssa_5.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_6
                };
                let ssa_8 = ssa_4.add_other(&ssa_7);
                let ssa_9 = ssa_8.add_base(&F::from_u32_unchecked(1u32));
                ssa_9
            };
            let ssa_16 = {
                let ssa_11 = base_field_scratch[5usize][subindex];
                let ssa_12 = base_field_scratch[6usize][subindex];
                let ssa_13 = ssa_11.add_other(&ssa_12);
                let ssa_14 = base_field_scratch[7usize][subindex];
                let ssa_15 = ssa_13.add_other(&ssa_14);
                ssa_15
            };
            let ssa_17 = ssa_10.mul_with_other(&ssa_16);
            ssa_17
        };
        let ssa_33 = {
            let ssa_19 = base_field_scratch[3usize][subindex];
            let ssa_31 = {
                let ssa_20 = base_field_scratch[29usize][subindex];
                let ssa_21 = base_field_scratch[37usize][subindex];
                let ssa_22 = ssa_20.add_other(&ssa_21);
                let ssa_25 = {
                    let ssa_23 = base_field_scratch[13usize][subindex];
                    let ssa_24 = ssa_23.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_24
                };
                let ssa_26 = ssa_22.add_other(&ssa_25);
                let ssa_29 = {
                    let ssa_27 = base_field_scratch[24usize][subindex];
                    let ssa_28 = ssa_27.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_28
                };
                let ssa_30 = ssa_26.add_other(&ssa_29);
                ssa_30
            };
            let ssa_32 = ssa_19.mul_with_other(&ssa_31);
            ssa_32
        };
        let ssa_34 = ssa_18.add_other(&ssa_33);
        let ssa_49 = {
            let ssa_35 = base_field_scratch[4usize][subindex];
            let ssa_47 = {
                let ssa_36 = base_field_scratch[0usize][subindex];
                let ssa_37 = base_field_scratch[40usize][subindex];
                let ssa_38 = ssa_36.add_other(&ssa_37);
                let ssa_41 = {
                    let ssa_39 = base_field_scratch[13usize][subindex];
                    let ssa_40 = ssa_39.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_40
                };
                let ssa_42 = ssa_38.add_other(&ssa_41);
                let ssa_45 = {
                    let ssa_43 = base_field_scratch[37usize][subindex];
                    let ssa_44 = ssa_43.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_44
                };
                let ssa_46 = ssa_42.add_other(&ssa_45);
                ssa_46
            };
            let ssa_48 = ssa_35.mul_with_other(&ssa_47);
            ssa_48
        };
        let ssa_50 = ssa_34.add_other(&ssa_49);
        let ssa_67 = {
            let ssa_51 = base_field_scratch[2usize][subindex];
            let ssa_65 = {
                let ssa_52 = base_field_scratch[0usize][subindex];
                let ssa_53 = base_field_scratch[24usize][subindex];
                let ssa_54 = ssa_52.add_other(&ssa_53);
                let ssa_55 = base_field_scratch[29usize][subindex];
                let ssa_56 = ssa_54.add_other(&ssa_55);
                let ssa_59 = {
                    let ssa_57 = base_field_scratch[13usize][subindex];
                    let ssa_58 = ssa_57.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_58
                };
                let ssa_60 = ssa_56.add_other(&ssa_59);
                let ssa_63 = {
                    let ssa_61 = base_field_scratch[37usize][subindex];
                    let ssa_62 = ssa_61.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_62
                };
                let ssa_64 = ssa_60.add_other(&ssa_63);
                ssa_64
            };
            let ssa_66 = ssa_51.mul_with_other(&ssa_65);
            ssa_66
        };
        let ssa_68 = ssa_50.add_other(&ssa_67);
        ssa_68
    };
    let val = ssa_69;
    val.mul_by_ext(&sumcheck_challenges[27usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_19_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_19_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_20_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_20_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_74 = {
        let ssa_17 = {
            let ssa_9 = {
                let ssa_0 = base_field_scratch[12usize][subindex];
                let ssa_1 = base_field_scratch[13usize][subindex];
                let ssa_2 = ssa_0.add_other(&ssa_1);
                let ssa_3 = base_field_scratch[38usize][subindex];
                let ssa_4 = ssa_2.add_other(&ssa_3);
                let ssa_7 = {
                    let ssa_5 = base_field_scratch[14usize][subindex];
                    let ssa_6 = ssa_5.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_6
                };
                let ssa_8 = ssa_4.add_other(&ssa_7);
                ssa_8
            };
            let ssa_15 = {
                let ssa_10 = base_field_scratch[5usize][subindex];
                let ssa_11 = base_field_scratch[6usize][subindex];
                let ssa_12 = ssa_10.add_other(&ssa_11);
                let ssa_13 = base_field_scratch[7usize][subindex];
                let ssa_14 = ssa_12.add_other(&ssa_13);
                ssa_14
            };
            let ssa_16 = ssa_9.mul_with_other(&ssa_15);
            ssa_16
        };
        let ssa_34 = {
            let ssa_18 = base_field_scratch[3usize][subindex];
            let ssa_32 = {
                let ssa_19 = base_field_scratch[13usize][subindex];
                let ssa_20 = base_field_scratch[30usize][subindex];
                let ssa_21 = ssa_19.add_other(&ssa_20);
                let ssa_22 = base_field_scratch[38usize][subindex];
                let ssa_23 = ssa_21.add_other(&ssa_22);
                let ssa_26 = {
                    let ssa_24 = base_field_scratch[14usize][subindex];
                    let ssa_25 = ssa_24.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_25
                };
                let ssa_27 = ssa_23.add_other(&ssa_26);
                let ssa_30 = {
                    let ssa_28 = base_field_scratch[25usize][subindex];
                    let ssa_29 = ssa_28.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_29
                };
                let ssa_31 = ssa_27.add_other(&ssa_30);
                ssa_31
            };
            let ssa_33 = ssa_18.mul_with_other(&ssa_32);
            ssa_33
        };
        let ssa_35 = ssa_17.add_other(&ssa_34);
        let ssa_52 = {
            let ssa_36 = base_field_scratch[4usize][subindex];
            let ssa_50 = {
                let ssa_37 = base_field_scratch[1usize][subindex];
                let ssa_38 = base_field_scratch[13usize][subindex];
                let ssa_39 = ssa_37.add_other(&ssa_38);
                let ssa_40 = base_field_scratch[41usize][subindex];
                let ssa_41 = ssa_39.add_other(&ssa_40);
                let ssa_44 = {
                    let ssa_42 = base_field_scratch[14usize][subindex];
                    let ssa_43 = ssa_42.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_43
                };
                let ssa_45 = ssa_41.add_other(&ssa_44);
                let ssa_48 = {
                    let ssa_46 = base_field_scratch[38usize][subindex];
                    let ssa_47 = ssa_46.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_47
                };
                let ssa_49 = ssa_45.add_other(&ssa_48);
                ssa_49
            };
            let ssa_51 = ssa_36.mul_with_other(&ssa_50);
            ssa_51
        };
        let ssa_53 = ssa_35.add_other(&ssa_52);
        let ssa_72 = {
            let ssa_54 = base_field_scratch[2usize][subindex];
            let ssa_70 = {
                let ssa_55 = base_field_scratch[1usize][subindex];
                let ssa_56 = base_field_scratch[13usize][subindex];
                let ssa_57 = ssa_55.add_other(&ssa_56);
                let ssa_58 = base_field_scratch[25usize][subindex];
                let ssa_59 = ssa_57.add_other(&ssa_58);
                let ssa_60 = base_field_scratch[30usize][subindex];
                let ssa_61 = ssa_59.add_other(&ssa_60);
                let ssa_64 = {
                    let ssa_62 = base_field_scratch[14usize][subindex];
                    let ssa_63 = ssa_62.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_63
                };
                let ssa_65 = ssa_61.add_other(&ssa_64);
                let ssa_68 = {
                    let ssa_66 = base_field_scratch[38usize][subindex];
                    let ssa_67 = ssa_66.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_67
                };
                let ssa_69 = ssa_65.add_other(&ssa_68);
                ssa_69
            };
            let ssa_71 = ssa_54.mul_with_other(&ssa_70);
            ssa_71
        };
        let ssa_73 = ssa_53.add_other(&ssa_72);
        ssa_73
    };
    let val = ssa_74;
    val.mul_by_ext(&sumcheck_challenges[28usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_20_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_75 = {
        let ssa_18 = {
            let ssa_10 = {
                let ssa_0 = base_field_scratch[12usize][subindex];
                let ssa_1 = base_field_scratch[13usize][subindex];
                let ssa_2 = ssa_0.add_other(&ssa_1);
                let ssa_3 = base_field_scratch[38usize][subindex];
                let ssa_4 = ssa_2.add_other(&ssa_3);
                let ssa_7 = {
                    let ssa_5 = base_field_scratch[14usize][subindex];
                    let ssa_6 = ssa_5.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_6
                };
                let ssa_8 = ssa_4.add_other(&ssa_7);
                let ssa_9 = ssa_8.add_base(&F::from_u32_unchecked(30720u32));
                ssa_9
            };
            let ssa_16 = {
                let ssa_11 = base_field_scratch[5usize][subindex];
                let ssa_12 = base_field_scratch[6usize][subindex];
                let ssa_13 = ssa_11.add_other(&ssa_12);
                let ssa_14 = base_field_scratch[7usize][subindex];
                let ssa_15 = ssa_13.add_other(&ssa_14);
                ssa_15
            };
            let ssa_17 = ssa_10.mul_with_other(&ssa_16);
            ssa_17
        };
        let ssa_35 = {
            let ssa_19 = base_field_scratch[3usize][subindex];
            let ssa_33 = {
                let ssa_20 = base_field_scratch[13usize][subindex];
                let ssa_21 = base_field_scratch[30usize][subindex];
                let ssa_22 = ssa_20.add_other(&ssa_21);
                let ssa_23 = base_field_scratch[38usize][subindex];
                let ssa_24 = ssa_22.add_other(&ssa_23);
                let ssa_27 = {
                    let ssa_25 = base_field_scratch[14usize][subindex];
                    let ssa_26 = ssa_25.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_26
                };
                let ssa_28 = ssa_24.add_other(&ssa_27);
                let ssa_31 = {
                    let ssa_29 = base_field_scratch[25usize][subindex];
                    let ssa_30 = ssa_29.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_30
                };
                let ssa_32 = ssa_28.add_other(&ssa_31);
                ssa_32
            };
            let ssa_34 = ssa_19.mul_with_other(&ssa_33);
            ssa_34
        };
        let ssa_36 = ssa_18.add_other(&ssa_35);
        let ssa_53 = {
            let ssa_37 = base_field_scratch[4usize][subindex];
            let ssa_51 = {
                let ssa_38 = base_field_scratch[1usize][subindex];
                let ssa_39 = base_field_scratch[13usize][subindex];
                let ssa_40 = ssa_38.add_other(&ssa_39);
                let ssa_41 = base_field_scratch[41usize][subindex];
                let ssa_42 = ssa_40.add_other(&ssa_41);
                let ssa_45 = {
                    let ssa_43 = base_field_scratch[14usize][subindex];
                    let ssa_44 = ssa_43.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_44
                };
                let ssa_46 = ssa_42.add_other(&ssa_45);
                let ssa_49 = {
                    let ssa_47 = base_field_scratch[38usize][subindex];
                    let ssa_48 = ssa_47.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_48
                };
                let ssa_50 = ssa_46.add_other(&ssa_49);
                ssa_50
            };
            let ssa_52 = ssa_37.mul_with_other(&ssa_51);
            ssa_52
        };
        let ssa_54 = ssa_36.add_other(&ssa_53);
        let ssa_73 = {
            let ssa_55 = base_field_scratch[2usize][subindex];
            let ssa_71 = {
                let ssa_56 = base_field_scratch[1usize][subindex];
                let ssa_57 = base_field_scratch[13usize][subindex];
                let ssa_58 = ssa_56.add_other(&ssa_57);
                let ssa_59 = base_field_scratch[25usize][subindex];
                let ssa_60 = ssa_58.add_other(&ssa_59);
                let ssa_61 = base_field_scratch[30usize][subindex];
                let ssa_62 = ssa_60.add_other(&ssa_61);
                let ssa_65 = {
                    let ssa_63 = base_field_scratch[14usize][subindex];
                    let ssa_64 = ssa_63.mul_by_base(&F::from_u32_unchecked(2013200385u32));
                    ssa_64
                };
                let ssa_66 = ssa_62.add_other(&ssa_65);
                let ssa_69 = {
                    let ssa_67 = base_field_scratch[38usize][subindex];
                    let ssa_68 = ssa_67.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_68
                };
                let ssa_70 = ssa_66.add_other(&ssa_69);
                ssa_70
            };
            let ssa_72 = ssa_55.mul_with_other(&ssa_71);
            ssa_72
        };
        let ssa_74 = ssa_54.add_other(&ssa_73);
        ssa_74
    };
    let val = ssa_75;
    val.mul_by_ext(&sumcheck_challenges[28usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_20_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_20_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_21_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_21_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[29usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[29usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_21_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[29usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[29usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_21_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_21_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_22_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_22_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[30usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[30usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_22_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[30usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[30usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_22_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_22_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_23_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_23_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[27usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[31usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_23_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[27usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[31usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_23_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_23_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_24_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_24_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[28usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[32usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_24_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[28usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[32usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_24_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_24_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_25_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_25_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[37usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[33usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_25_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[37usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[33usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_25_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_25_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_26_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_26_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[38usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[34usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_26_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_3 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_1 = base_field_scratch[38usize][subindex];
        let ssa_2 = ssa_0.mul_with_other(&ssa_1);
        ssa_2
    };
    let val = ssa_3;
    val.mul_by_ext(&sumcheck_challenges[34usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_26_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_26_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_27_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_27_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_17 = {
        let ssa_5 = {
            let ssa_0 = base_field_scratch[40usize][subindex];
            let ssa_3 = {
                let ssa_1 = base_field_scratch[44usize][subindex];
                let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                ssa_2
            };
            let ssa_4 = ssa_0.add_other(&ssa_3);
            ssa_4
        };
        let ssa_14 = {
            let ssa_13 = {
                let ssa_11 = {
                    let ssa_6 = base_field_scratch[40usize][subindex];
                    let ssa_9 = {
                        let ssa_7 = base_field_scratch[44usize][subindex];
                        let ssa_8 = ssa_7.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                        ssa_8
                    };
                    let ssa_10 = ssa_6.add_other(&ssa_9);
                    ssa_10
                };
                let ssa_12 = ssa_11.mul_by_base(&F::from_u32_unchecked(2013235201u32));
                ssa_12
            };
            ssa_13
        };
        let ssa_15 = ssa_5.mul_with_other(&ssa_14);
        let ssa_16 = ssa_15.mul_by_base(&F::from_u32_unchecked(2013235201u32));
        ssa_16
    };
    let val = ssa_17;
    val.mul_by_ext(&sumcheck_challenges[35usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_27_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_20 = {
        let ssa_6 = {
            let ssa_0 = base_field_scratch[40usize][subindex];
            let ssa_3 = {
                let ssa_1 = base_field_scratch[44usize][subindex];
                let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                ssa_2
            };
            let ssa_4 = ssa_0.add_other(&ssa_3);
            let ssa_5 = ssa_4.add_base(&F::from_u32_unchecked(4u32));
            ssa_5
        };
        let ssa_17 = {
            let ssa_15 = {
                let ssa_13 = {
                    let ssa_7 = base_field_scratch[40usize][subindex];
                    let ssa_10 = {
                        let ssa_8 = base_field_scratch[44usize][subindex];
                        let ssa_9 = ssa_8.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                        ssa_9
                    };
                    let ssa_11 = ssa_7.add_other(&ssa_10);
                    let ssa_12 = ssa_11.add_base(&F::from_u32_unchecked(4u32));
                    ssa_12
                };
                let ssa_14 = ssa_13.mul_by_base(&F::from_u32_unchecked(2013235201u32));
                ssa_14
            };
            let ssa_16 = ssa_15.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_16
        };
        let ssa_18 = ssa_6.mul_with_other(&ssa_17);
        let ssa_19 = ssa_18.mul_by_base(&F::from_u32_unchecked(2013235201u32));
        ssa_19
    };
    let val = ssa_20;
    val.mul_by_ext(&sumcheck_challenges[35usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_27_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_27_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_28_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_28_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_15 = {
        let ssa_0 = base_field_scratch[41usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[45usize][subindex];
            let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.add_other(&ssa_3);
        let ssa_13 = {
            let ssa_11 = {
                let ssa_5 = base_field_scratch[40usize][subindex];
                let ssa_8 = {
                    let ssa_6 = base_field_scratch[44usize][subindex];
                    let ssa_7 = ssa_6.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_7
                };
                let ssa_9 = ssa_5.add_other(&ssa_8);
                let ssa_10 = ssa_9.add_base(&F::from_u32_unchecked(4u32));
                ssa_10
            };
            let ssa_12 = ssa_11.mul_by_base(&F::from_u32_unchecked(2013235201u32));
            ssa_12
        };
        let ssa_14 = ssa_4.add_other(&ssa_13);
        ssa_14
    };
    let val = ssa_15;
    val.mul_by_ext(&sumcheck_challenges[36usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_28_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    [E::ZERO, E::ZERO]
}
#[inline(always)]
pub fn fetch_layer_0_gate_29_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_29_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_15 = {
        let ssa_14 = {
            let ssa_5 = {
                let ssa_0 = base_field_scratch[42usize][subindex];
                let ssa_3 = {
                    let ssa_1 = base_field_scratch[46usize][subindex];
                    let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_2
                };
                let ssa_4 = ssa_0.add_other(&ssa_3);
                ssa_4
            };
            let ssa_11 = {
                let ssa_6 = base_field_scratch[42usize][subindex];
                let ssa_9 = {
                    let ssa_7 = base_field_scratch[46usize][subindex];
                    let ssa_8 = ssa_7.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_8
                };
                let ssa_10 = ssa_6.add_other(&ssa_9);
                ssa_10
            };
            let ssa_12 = ssa_5.mul_with_other(&ssa_11);
            let ssa_13 = ssa_12.mul_by_base(&F::from_u32_unchecked(14745600u32));
            ssa_13
        };
        ssa_14
    };
    let val = ssa_15;
    val.mul_by_ext(&sumcheck_challenges[37usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_29_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_27 = {
        let ssa_16 = {
            let ssa_6 = {
                let ssa_0 = base_field_scratch[42usize][subindex];
                let ssa_3 = {
                    let ssa_1 = base_field_scratch[46usize][subindex];
                    let ssa_2 = ssa_1.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_2
                };
                let ssa_4 = ssa_0.add_other(&ssa_3);
                let ssa_5 = ssa_4.add_base(&F::from_u32_unchecked(4u32));
                ssa_5
            };
            let ssa_13 = {
                let ssa_7 = base_field_scratch[42usize][subindex];
                let ssa_10 = {
                    let ssa_8 = base_field_scratch[46usize][subindex];
                    let ssa_9 = ssa_8.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_9
                };
                let ssa_11 = ssa_7.add_other(&ssa_10);
                let ssa_12 = ssa_11.add_base(&F::from_u32_unchecked(4u32));
                ssa_12
            };
            let ssa_14 = ssa_6.mul_with_other(&ssa_13);
            let ssa_15 = ssa_14.mul_by_base(&F::from_u32_unchecked(14745600u32));
            ssa_15
        };
        let ssa_25 = {
            let ssa_23 = {
                let ssa_17 = base_field_scratch[42usize][subindex];
                let ssa_20 = {
                    let ssa_18 = base_field_scratch[46usize][subindex];
                    let ssa_19 = ssa_18.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_19
                };
                let ssa_21 = ssa_17.add_other(&ssa_20);
                let ssa_22 = ssa_21.add_base(&F::from_u32_unchecked(4u32));
                ssa_22
            };
            let ssa_24 = ssa_23.mul_by_base(&F::from_u32_unchecked(3840u32));
            ssa_24
        };
        let ssa_26 = ssa_16.add_base_repr(&ssa_25);
        ssa_26
    };
    let val = ssa_27;
    val.mul_by_ext(&sumcheck_challenges[37usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_29_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_29_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_30_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_30_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_15 = {
        let ssa_0 = base_field_scratch[47usize][subindex];
        let ssa_9 = {
            let ssa_7 = {
                let ssa_1 = base_field_scratch[42usize][subindex];
                let ssa_4 = {
                    let ssa_2 = base_field_scratch[46usize][subindex];
                    let ssa_3 = ssa_2.mul_by_base(&F::from_u32_unchecked(2013265920u32));
                    ssa_3
                };
                let ssa_5 = ssa_1.add_other(&ssa_4);
                let ssa_6 = ssa_5.add_base(&F::from_u32_unchecked(4u32));
                ssa_6
            };
            let ssa_8 = ssa_7.mul_by_base(&F::from_u32_unchecked(3840u32));
            ssa_8
        };
        let ssa_10 = ssa_0.add_other(&ssa_9);
        let ssa_13 = {
            let ssa_11 = base_field_scratch[43usize][subindex];
            let ssa_12 = ssa_11.mul_by_base(&F::from_u32_unchecked(2013265920u32));
            ssa_12
        };
        let ssa_14 = ssa_10.add_other(&ssa_13);
        ssa_14
    };
    let val = ssa_15;
    val.mul_by_ext(&sumcheck_challenges[38usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_30_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    [E::ZERO, E::ZERO]
}
#[inline(always)]
pub fn fetch_layer_0_gate_31_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_31_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[2usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[2usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[39usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_31_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[2usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[2usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[39usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_31_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_31_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_32_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_32_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[3usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[3usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[40usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_32_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[3usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[3usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[40usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_32_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_32_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_33_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_33_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[4usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[4usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[41usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_33_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[4usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[4usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[41usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_33_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_33_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_34_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_34_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[5usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[5usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[42usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_34_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[5usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[5usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[42usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_34_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_34_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_35_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_35_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[6usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[6usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[43usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_35_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[6usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[6usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[43usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_35_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_35_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_36_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_36_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[7usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[7usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[44usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_36_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[7usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[7usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[44usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_36_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_36_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_37_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_37_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[8usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[8usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[45usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_37_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[8usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[8usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[45usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_37_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_37_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_38_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_38_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[9usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[46usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_38_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[9usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[9usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[46usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_38_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_38_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_39_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_39_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[10usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[10usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[47usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_39_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[10usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[10usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[47usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_39_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_39_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_40_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_40_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[13usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[13usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[48usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_40_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[13usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[13usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[48usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_40_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_40_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_41_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_41_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[14usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[14usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[49usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_41_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[14usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[14usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[49usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_41_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_41_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_42_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_42_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[16usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[16usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[50usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_42_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[16usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[16usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[50usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_42_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_42_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_43_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_43_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[17usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[17usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[51usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_43_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[17usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[17usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[51usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_43_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_43_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_44_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
fn compute_layer_0_gate_44_quadratic_part_only<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const N: usize,
>(
    base_field_scratch: &[[S::BaseFieldInput; N]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let ssa_4 = {
        let ssa_0 = base_field_scratch[18usize][subindex];
        let ssa_2 = {
            let ssa_1 = base_field_scratch[18usize][subindex];
            ssa_1
        };
        let ssa_3 = ssa_0.mul_with_other(&ssa_2);
        ssa_3
    };
    let val = ssa_4;
    val.mul_by_ext(&sumcheck_challenges[52usize], base_repr_ctx)
}
#[inline(always)]
fn compute_layer_0_gate_44_explicit<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    sumcheck_challenges: &[E; 53usize],
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let ssa_5 = {
        let ssa_0 = base_field_scratch[18usize][subindex];
        let ssa_3 = {
            let ssa_1 = base_field_scratch[18usize][subindex];
            let ssa_2 = ssa_1.add_base(&F::from_u32_unchecked(2013265920u32));
            ssa_2
        };
        let ssa_4 = ssa_0.mul_with_other(&ssa_3);
        ssa_4
    };
    let val = ssa_5;
    val.mul_by_ext(&sumcheck_challenges[52usize], base_repr_ctx)
}
#[inline(always)]
pub fn compute_layer_0_gate_44_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 1usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let c1 = unsafe {
        let base_field_scratch =
            core::mem::transmute::<_, &[[S::BaseFieldInput; 1]; 50usize]>(base_field_scratch);
        compute_layer_0_gate_44_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            0,
        )
    };
    [E::ZERO, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_0<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[39usize] =
        all_base_inputs[39usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_0<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    if EXPLICIT_FORM {
        let c0 =
            base_field_scratch[39usize][0].mul_by_ext(&sumcheck_challenges[0usize], base_repr_ctx);
        let c1 =
            base_field_scratch[39usize][1].mul_by_ext(&sumcheck_challenges[0usize], base_repr_ctx);
        [c0, c1]
    } else {
        let c0 =
            base_field_scratch[39usize][0].mul_by_ext(&sumcheck_challenges[0usize], base_repr_ctx);
        [c0, E::ZERO]
    }
}
#[inline(always)]
pub fn fetch_layer_0_gate_1<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[22usize] =
        all_base_inputs[22usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[23usize] =
        all_base_inputs[23usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[24usize] =
        all_base_inputs[24usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[25usize] =
        all_base_inputs[25usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[26usize] =
        all_base_inputs[26usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[27usize] =
        all_base_inputs[27usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[28usize] =
        all_base_inputs[28usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[29usize] =
        all_base_inputs[29usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[30usize] =
        all_base_inputs[30usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[31usize] =
        all_base_inputs[31usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_1<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let mut c0 = compute_layer_0_gate_1_explicit::<F, E, S>(
        base_field_scratch,
        external_challenges,
        base_repr_ctx,
        0,
    );
    c0.mul_assign(&sumcheck_challenges[1usize]);
    let mut c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_1_explicit::<F, E, S>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_1_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    };
    c1.mul_assign(&sumcheck_challenges[1usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_2<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[42usize] =
        all_base_inputs[42usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[43usize] =
        all_base_inputs[43usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_2<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let mut c0 = compute_layer_0_gate_2_explicit::<F, E, S>(
        base_field_scratch,
        external_challenges,
        base_repr_ctx,
        0,
    );
    c0.mul_assign(&sumcheck_challenges[2usize]);
    let mut c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_2_explicit::<F, E, S>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_2_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    };
    c1.mul_assign(&sumcheck_challenges[2usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_3<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[32usize] =
        all_base_inputs[32usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[33usize] =
        all_base_inputs[33usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[34usize] =
        all_base_inputs[34usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[35usize] =
        all_base_inputs[35usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[36usize] =
        all_base_inputs[36usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[40usize] =
        all_base_inputs[40usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[41usize] =
        all_base_inputs[41usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_3<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let mut c0 = compute_layer_0_gate_3_explicit::<F, E, S>(
        base_field_scratch,
        external_challenges,
        base_repr_ctx,
        0,
    );
    c0.mul_assign(&sumcheck_challenges[3usize]);
    let mut c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_3_explicit::<F, E, S>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_3_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    };
    c1.mul_assign(&sumcheck_challenges[3usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_4<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[37usize] =
        all_base_inputs[37usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[38usize] =
        all_base_inputs[38usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[44usize] =
        all_base_inputs[44usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[45usize] =
        all_base_inputs[45usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[46usize] =
        all_base_inputs[46usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[47usize] =
        all_base_inputs[47usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_4<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let mut c0 = compute_layer_0_gate_4_explicit::<F, E, S>(
        base_field_scratch,
        external_challenges,
        base_repr_ctx,
        0,
    );
    c0.mul_assign(&sumcheck_challenges[4usize]);
    let mut c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_4_explicit::<F, E, S>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_4_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            external_challenges,
            base_repr_ctx,
            1,
        )
    };
    c1.mul_assign(&sumcheck_challenges[4usize]);
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_5<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[11usize] =
        all_base_inputs[11usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[19usize] =
        all_base_inputs[19usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[48usize] =
        all_base_inputs[48usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_5<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_5_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_5_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_5_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_6<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[12usize] =
        all_base_inputs[12usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_6<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_6_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_6_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_6_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_7<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_7<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_7_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_7_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_7_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_8<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_8<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    if EXPLICIT_FORM {
        let c0 =
            base_field_scratch[45usize][0].mul_by_ext(&sumcheck_challenges[11usize], base_repr_ctx);
        let c1 =
            base_field_scratch[45usize][1].mul_by_ext(&sumcheck_challenges[11usize], base_repr_ctx);
        [c0, c1]
    } else {
        let c0 =
            base_field_scratch[45usize][0].mul_by_ext(&sumcheck_challenges[11usize], base_repr_ctx);
        [c0, E::ZERO]
    }
}
#[inline(always)]
pub fn fetch_layer_0_gate_9<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[20usize] =
        all_base_inputs[20usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[49usize] =
        all_base_inputs[49usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_9<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_9_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_9_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_9_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_10<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[16usize] =
        all_base_inputs[16usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_10<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_10_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_10_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_10_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_11<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[17usize] =
        all_base_inputs[17usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_11<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_11_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_11_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_11_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_12<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[18usize] =
        all_base_inputs[18usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_12<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_12_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        lookup_gamma,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_12_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_12_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            lookup_gamma,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_13<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_13<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_13_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_13_explicit::<F, E, S>(
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
#[inline(always)]
pub fn fetch_layer_0_gate_14<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[0usize] =
        all_base_inputs[0usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[1usize] =
        all_base_inputs[1usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[2usize] =
        all_base_inputs[2usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[3usize] =
        all_base_inputs[3usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[4usize] =
        all_base_inputs[4usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[5usize] =
        all_base_inputs[5usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[6usize] =
        all_base_inputs[6usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[7usize] =
        all_base_inputs[7usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[8usize] =
        all_base_inputs[8usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[9usize] =
        all_base_inputs[9usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[10usize] =
        all_base_inputs[10usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    base_field_scratch[21usize] =
        all_base_inputs[21usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
    ext_field_scratch[0usize] =
        all_ext_inputs[0usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_14<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_14_explicit::<F, E, S>(
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
        compute_layer_0_gate_14_explicit::<F, E, S>(
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
        compute_layer_0_gate_14_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            ext_field_scratch,
            sumcheck_challenges,
            lookup_alpha_powers,
            base_repr_ctx,
            ext_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_15<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_15<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_15_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_15_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_15_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_16<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[15usize] =
        all_base_inputs[15usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_16<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_16_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_16_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_16_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_17<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_17<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_17_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_17_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_17_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_18<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[14usize] =
        all_base_inputs[14usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_18<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_18_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_18_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_18_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_19<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
    base_field_scratch[13usize] =
        all_base_inputs[13usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn compute_layer_0_gate_19<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_19_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_19_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_19_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_20<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_20<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_20_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_20_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_20_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_21<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_21<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_21_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_21_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_21_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_22<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_22<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_22_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_22_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_22_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_23<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_23<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_23_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_23_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_23_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_24<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_24<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_24_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_24_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_24_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_25<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_25<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_25_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_25_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_25_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_26<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_26<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_26_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_26_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_26_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_27<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_27<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_27_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_27_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_27_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_28<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_28<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_28_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_28_explicit::<F, E, S>(
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
#[inline(always)]
pub fn fetch_layer_0_gate_29<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_29<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_29_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_29_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_29_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_30<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_30<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_30_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_30_explicit::<F, E, S>(
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
#[inline(always)]
pub fn fetch_layer_0_gate_31<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_31<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_31_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_31_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_31_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_32<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_32<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_32_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_32_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_32_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_33<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_33<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_33_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_33_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_33_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_34<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_34<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_34_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_34_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_34_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_35<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_35<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_35_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_35_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_35_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_36<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_36<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_36_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_36_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_36_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_37<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_37<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_37_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_37_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_37_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_38<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_38<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_38_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_38_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_38_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_39<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_39<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_39_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_39_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_39_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_40<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_40<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_40_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_40_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_40_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_41<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_41<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_41_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_41_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_41_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_42<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_42<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_42_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_42_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_42_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_43<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_43<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_43_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_43_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_43_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
#[inline(always)]
pub fn fetch_layer_0_gate_44<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 1usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 1usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn compute_layer_0_gate_44<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &[[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 1usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &impl GKRExternalChallengesProvider<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
) -> [E; 2] {
    let c0 = compute_layer_0_gate_44_explicit::<F, E, S>(
        base_field_scratch,
        sumcheck_challenges,
        base_repr_ctx,
        0,
    );
    let c1 = if EXPLICIT_FORM {
        compute_layer_0_gate_44_explicit::<F, E, S>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    } else {
        compute_layer_0_gate_44_quadratic_part_only::<F, E, S, _>(
            base_field_scratch,
            sumcheck_challenges,
            base_repr_ctx,
            1,
        )
    };
    [c0, c1]
}
pub fn layer_0_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    C: GKRExternalChallengesProvider<F, E>,
>(
    all_base_inputs: &[S::BaseInputAccessor],
    all_ext_inputs: &[S::ExtInputAccessor],
    all_base_outputs: &[S::BaseInputAccessor],
    all_ext_outputs: &[S::ExtInputAccessor],
    sumcheck_challenges: &[E],
    external_challenges: &C,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    eq_poly_precomputed: &[E],
    row_range: core::ops::Range<usize>,
) -> [E; 2] {
    let all_base_inputs = all_base_inputs
        .as_array::<50usize>()
        .expect("must have proper length");
    let all_ext_inputs = all_ext_inputs
        .as_array::<1usize>()
        .expect("must have proper length");
    let all_base_outputs = all_base_outputs
        .as_array::<3usize>()
        .expect("must have proper length");
    let all_ext_outputs = all_ext_outputs
        .as_array::<20usize>()
        .expect("must have proper length");
    let sumcheck_challenges = sumcheck_challenges
        .as_array::<53usize>()
        .expect("must have proper length");
    let mut base_field_scratch: [_; 50usize] = std::array::from_fn(|_| S::BaseFieldInput::zero());
    let mut ext_field_scratch: [_; 1usize] = std::array::from_fn(|_| S::ExtFieldInput::zero());
    let mut accumulated = [E::ZERO; 2];
    for row_index in row_range {
        let mut result = [E::ZERO; 2];
        fetch_layer_0_gate_0_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_0_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_1_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_1_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_2_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_2_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_3_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_3_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_4_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_4_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_5_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_5_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_6_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_6_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_7_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_7_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_8_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_8_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_9_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_9_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_10_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_10_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_11_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_11_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_12_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_12_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_13_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_13_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_14_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_14_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_15_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_15_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_16_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_16_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_17_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_17_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_18_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_18_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_19_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_19_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_20_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_20_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_21_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_21_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_22_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_22_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_23_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_23_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_24_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_24_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_25_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_25_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_26_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_26_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_27_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_27_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_28_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_28_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_29_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_29_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_30_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_30_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_31_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_31_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_32_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_32_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_33_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_33_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_34_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_34_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_35_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_35_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_36_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_36_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_37_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_37_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_38_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_38_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_39_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_39_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_40_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_40_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_41_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_41_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_42_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_42_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_43_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_43_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_44_initial_round::<F, E, S>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_44_initial_round::<F, E, S>(
            &base_field_scratch,
            &ext_field_scratch,
            all_base_outputs,
            all_ext_outputs,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
            row_index,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        let eq = eq_poly_precomputed[row_index];
        result[0].mul_assign(&eq);
        result[1].mul_assign(&eq);
        accumulated[0].add_assign(&result[0]);
        accumulated[1].add_assign(&result[1]);
    }
    accumulated
}
pub fn layer_0<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    C: GKRExternalChallengesProvider<F, E>,
    const EXPLICIT_FORM: bool,
>(
    all_base_inputs: &[S::BaseInputAccessor],
    all_ext_inputs: &[S::ExtInputAccessor],
    sumcheck_challenges: &[E],
    external_challenges: &C,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    eq_poly_precomputed: &[E],
    row_range: core::ops::Range<usize>,
) -> [E; 2] {
    let all_base_inputs = all_base_inputs
        .as_array::<50usize>()
        .expect("must have proper length");
    let all_ext_inputs = all_ext_inputs
        .as_array::<1usize>()
        .expect("must have proper length");
    let sumcheck_challenges = sumcheck_challenges
        .as_array::<53usize>()
        .expect("must have proper length");
    let mut base_field_scratch: [_; 50usize] =
        std::array::from_fn(|_| [S::BaseFieldInput::zero(); 2]);
    let mut ext_field_scratch: [_; 1usize] = std::array::from_fn(|_| [S::ExtFieldInput::zero(); 2]);
    let mut accumulated = [E::ZERO; 2];
    for row_index in row_range {
        let mut result = [E::ZERO; 2];
        fetch_layer_0_gate_0::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_0::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_1::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_1::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_2::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_2::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_3::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_3::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_4::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_4::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_5::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_5::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_6::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_6::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_7::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_7::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_8::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_8::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_9::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_9::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_10::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_10::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_11::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_11::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_12::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_12::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_13::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_13::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_14::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_14::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_15::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_15::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_16::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_16::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_17::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_17::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_18::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_18::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_19::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_19::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_20::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_20::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_21::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_21::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_22::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_22::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_23::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_23::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_24::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_24::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_25::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_25::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_26::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_26::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_27::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_27::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_28::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_28::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_29::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_29::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_30::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_30::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_31::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_31::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_32::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_32::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_33::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_33::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_34::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_34::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_35::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_35::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_36::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_36::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_37::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_37::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_38::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_38::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_39::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_39::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_40::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_40::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_41::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_41::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_42::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_42::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_43::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_43::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        fetch_layer_0_gate_44::<F, E, S, EXPLICIT_FORM>(
            &mut base_field_scratch,
            &mut ext_field_scratch,
            all_base_inputs,
            all_ext_inputs,
            row_index,
        );
        let [e0, e1] = compute_layer_0_gate_44::<F, E, S, EXPLICIT_FORM>(
            &base_field_scratch,
            &ext_field_scratch,
            sumcheck_challenges,
            external_challenges,
            lookup_alpha_powers,
            lookup_gamma,
            base_repr_ctx,
            ext_repr_ctx,
        );
        result[0].add_assign(&e0);
        result[1].add_assign(&e1);
        let eq = eq_poly_precomputed[row_index];
        result[0].mul_assign(&eq);
        result[1].mul_assign(&eq);
        accumulated[0].add_assign(&result[0]);
        accumulated[1].add_assign(&result[1]);
    }
    accumulated
}
