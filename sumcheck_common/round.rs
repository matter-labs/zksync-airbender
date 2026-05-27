#[inline(always)]
pub fn fetch_layer_0_gate_0<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
    ext_field_scratch: &[[S::ExtFieldInput; 2]; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
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
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_14<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
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
}
#[inline(always)]
pub fn fetch_layer_0_gate_15<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_16<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
    base_field_scratch[15usize] =
        all_base_inputs[15usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn fetch_layer_0_gate_17<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_18<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
    base_field_scratch[14usize] =
        all_base_inputs[14usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn fetch_layer_0_gate_19<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
    base_field_scratch[13usize] =
        all_base_inputs[13usize].get_two_points::<false, EXPLICIT_FORM>(row_index);
}
#[inline(always)]
pub fn fetch_layer_0_gate_20<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_21<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_22<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_23<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_24<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_25<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_26<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_27<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_28<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_29<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_30<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_31<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_32<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_33<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_34<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_35<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_36<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_37<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_38<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_39<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_40<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_41<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_42<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_43<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
#[inline(always)]
pub fn fetch_layer_0_gate_44<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    base_field_scratch: &mut [[S::BaseFieldInput; 2]; 50usize],
    ext_field_scratch: &mut [[S::ExtFieldInput; 2]; 0usize],
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    row_index: usize,
) {
}
pub fn layer_0<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: SumcheckRoundSource<F, E>,
    const EXPLICIT_FORM: bool,
>(
    all_base_inputs: &[S::BaseInputAccessor; 50usize],
    all_ext_inputs: &[S::ExtInputAccessor; 0usize],
    sumcheck_challenges: &[E; 53usize],
    external_challenges: &GKRExternalChallenges<F, E>,
    lookup_alpha_powers: &[E],
    lookup_gamma: &E,
    base_repr_ctx: &<S::BaseFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    ext_repr_ctx: &<S::ExtFieldInput as EvaluationRepresentaionBase<F, E>>::CTX,
    row_index: usize,
) -> [E; 2] {
    let mut base_field_scratch: [_; 50usize] =
        std::array::from_fn(|_| [S::BaseFieldInput::zero(); 2]);
    let mut ext_field_scratch: [_; 0usize] = std::array::from_fn(|_| [S::ExtFieldInput::zero(); 2]);
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
    result
}
