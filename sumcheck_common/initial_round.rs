#[inline(always)]
pub fn fetch_layer_0_gate_0_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(0u32));
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[22usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(0u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[23usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(0u32));
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[27usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(0u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[28usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[22usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[23usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[27usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[28usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[30usize][1].mul_by_ext(&t, base_repr_ctx);
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(0u32));
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(0u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(0u32));
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(1u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[26usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[24usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[25usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[31usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[29usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[30usize][1].mul_by_ext(&t, base_repr_ctx);
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(0u32));
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[32usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(0u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[33usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[34usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[35usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(2u32));
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(0u32));
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(0u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[40usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[32usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[33usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[34usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[35usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[40usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[41usize][1].mul_by_ext(&t, base_repr_ctx);
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(subindex < 2);
    }
    let mut acc = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(0u32));
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[42usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(2u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[37usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[38usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = external_challenges.permutation_argument_additive_part;
        acc.add_assign_base(&F::from_u32_unchecked(2u32));
        let mut t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        t.mul_assign_by_base(&F::from_u32_unchecked(0u32));
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let val = base_field_scratch[46usize][subindex];
        let val = val.add_base(&F::from_u32_unchecked(0u32));
        let t = val.mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[47usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[44usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
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
    external_challenges: &GKRExternalChallenges<F, E>,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    subindex: usize,
) -> E {
    unsafe {
        core::hint::assert_unchecked(N > 0);
        core::hint::assert_unchecked(subindex < N);
    }
    let mut acc = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        let t = base_field_scratch[36usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[42usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[43usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[37usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[38usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        acc
    };
    let mut acc_1 = {
        let mut acc = E::ZERO;
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
        let t = base_field_scratch[46usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        let t = base_field_scratch[47usize][subindex].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
        let t = base_field_scratch[44usize][1].mul_by_ext(&t, base_repr_ctx);
        acc.add_assign(&t);
        let t = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        let t = base_field_scratch[45usize][1].mul_by_ext(&t, base_repr_ctx);
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    let mut result = b.mul_by_ext(&a_plus_gamma, base_repr_ctx);
    result.add_assign(&c_plus_gamma);
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
    let mut result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[5usize], base_repr_ctx);
    let t = a
        .mul_with_other(&c)
        .mul_by_ext(&sumcheck_challenges[6usize], base_repr_ctx);
    result.add_assign(&t);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_5_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    let mut c1 = unsafe {
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    let mut result = b.mul_by_ext(&a_plus_gamma, base_repr_ctx);
    result.add_assign(&c_plus_gamma);
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
    let mut result = a
        .mul_with_other(&b)
        .mul_by_ext(&sumcheck_challenges[12usize], base_repr_ctx);
    let t = a
        .mul_with_other(&c)
        .mul_by_ext(&sumcheck_challenges[13usize], base_repr_ctx);
    result.add_assign(&t);
    result
}
#[inline(always)]
pub fn compute_layer_0_gate_9_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &[S::BaseFieldInput; 50usize],
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    let mut c1 = unsafe {
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
        let mut acc = base_field_scratch[42usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
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
        let mut acc = base_field_scratch[42usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
        let mut acc = base_field_scratch[43usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[23usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[16usize][subindex]);
        acc.add_assign(&F::from_u32_unchecked(524288u32));
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[27usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[17usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc.add_assign(&F::from_u32_unchecked(2013265920u32));
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
        let mut acc = base_field_scratch[43usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[23usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[16usize][subindex]);
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
        let mut acc = base_field_scratch[43usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[28usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[17usize][subindex]);
        acc.add_assign(&F::from_u32_unchecked(524288u32));
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[32usize][subindex]);
        acc = acc.add_other(
            &base_field_scratch[18usize][subindex].mul_by_base(&F::from_u32_unchecked(524288u32)),
        );
        acc.add_assign(&F::from_u32_unchecked(2013265919u32));
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
        let mut acc = base_field_scratch[43usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
        acc = acc.add_other(&base_field_scratch[28usize][subindex]);
        acc = acc.sub_other(&base_field_scratch[17usize][subindex]);
        acc
    };
    let b = {
        let mut acc = base_field_scratch[42usize][subindex]
            .mul_by_base(&F::from_u32_unchecked(2013265920u32));
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
    ext_field_scratch: &[S::ExtFieldInput; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_14_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
}
#[inline(always)]
pub fn fetch_layer_0_gate_15_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_16_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
    base_field_scratch[15usize] = all_base_inputs[15usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
pub fn fetch_layer_0_gate_17_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_18_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
    base_field_scratch[14usize] = all_base_inputs[14usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
pub fn fetch_layer_0_gate_19_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
    base_field_scratch[13usize] = all_base_inputs[13usize].get_f1_minus_f0_only::<false>(row_index);
}
#[inline(always)]
pub fn fetch_layer_0_gate_20_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_21_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_22_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_23_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_24_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_25_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_26_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_27_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_28_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_29_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_30_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_31_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_32_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_33_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_34_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_35_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_36_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_37_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_38_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_39_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_40_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_41_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_42_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_43_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_44_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    base_field_scratch: &mut [S::BaseFieldInput; 50usize],
    ext_field_scratch: &mut [S::ExtFieldInput; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
pub fn layer_0_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
>(
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    all_base_outputs: &[S::BaseInputAccessor; 3usize],
    all_ext_outputs: &[S::ExtInputAccessor; 20usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut base_field_scratch: [_; 50usize] = std::array::from_fn(|_| S::BaseFieldInput::zero());
    let mut ext_field_scratch: [_; 0usize] = std::array::from_fn(|_| S::ExtFieldInput::zero());
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
    result
}
