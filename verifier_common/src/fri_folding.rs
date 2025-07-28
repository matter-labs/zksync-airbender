use core::mem::MaybeUninit;

use field::{Field, FieldExtension, Mersenne31Complex, Mersenne31Field, Mersenne31Quartic};

#[allow(invalid_value)]
pub unsafe fn fri_fold_by_log_n<const FOLDING_DEGREE_LOG2: usize>(
    expected_value: &mut Mersenne31Quartic,
    evaluation_point: &mut Mersenne31Complex,
    domain_size_log_2: &mut usize,
    domain_index: &mut usize,
    tree_index: &mut usize,
    offset_inv: &mut Mersenne31Complex,
    leaf: &[Mersenne31Field],
    fri_folding_challenges_powers: &[Mersenne31Quartic],
    shared_factors_for_folding: &[Mersenne31Complex],
) {
    const MAX_SIZE_FOR_LEAF: usize = 32;
    const MAX_SIZE_FOR_ROOTS: usize = 16;

    assert!(FOLDING_DEGREE_LOG2 > 0);
    assert!(FOLDING_DEGREE_LOG2 <= 5);
    debug_assert_eq!(leaf.len(), (1 << FOLDING_DEGREE_LOG2) * 4);

    let in_leaf_mask: usize = (1 << FOLDING_DEGREE_LOG2) - 1;
    let eval_points_bits_mask = (1 << (*domain_size_log_2 - FOLDING_DEGREE_LOG2)) - 1;
    let generator_inv = Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED[*domain_size_log_2];

    *domain_size_log_2 -= FOLDING_DEGREE_LOG2;

    // here we use worst-case sizes
    let mut leaf_parsed =
        MaybeUninit::<[Mersenne31Quartic; MAX_SIZE_FOR_LEAF]>::uninit().assume_init();
    if core::mem::align_of::<Mersenne31Quartic>() != core::mem::align_of::<Mersenne31Field>() {
        let mut it = leaf.as_chunks::<4>().0.iter();
        for i in 0..(1 << FOLDING_DEGREE_LOG2) {
            // NOTE: field elements are reduced in the query already!
            *leaf_parsed.get_unchecked_mut(i) =
                Mersenne31Quartic::from_array_of_base(*it.next().unwrap_unchecked());
        }
    }

    let expected_index_in_rs_code_word_leaf = (*tree_index as usize) & in_leaf_mask;
    let value_at_expected_index = leaf
        .as_ptr()
        .add(expected_index_in_rs_code_word_leaf * 4)
        .cast::<[Mersenne31Field; 4]>();
    let value_at_expected_index =
        Mersenne31Quartic::from_array_of_base(value_at_expected_index.read());
    // check that our simulated value is actually in the leaf
    assert_eq!(*expected_value, value_at_expected_index);

    // note that our evaluation points share highest N-3 bits, so we can just precompute additional multiplication
    // factors for lower bits. We only need elements that are not negations of each other

    let shared_bits_in_folding = *domain_index & eval_points_bits_mask;
    let mut evaluation_point_shared_factor = generator_inv.pow(shared_bits_in_folding as u32);
    evaluation_point_shared_factor.mul_assign(&*offset_inv);
    // again - worst case size
    let mut folding_evals_points_inversed =
        MaybeUninit::<[Mersenne31Complex; MAX_SIZE_FOR_ROOTS]>::uninit().assume_init();
    for i in 0..(1 << (FOLDING_DEGREE_LOG2 - 1)) {
        let mut t = *shared_factors_for_folding.get_unchecked(i);
        t.mul_assign(&evaluation_point_shared_factor);
        *folding_evals_points_inversed.get_unchecked_mut(i) = t;
    }

    let mut buffer_0 =
        MaybeUninit::<[Mersenne31Quartic; MAX_SIZE_FOR_LEAF]>::uninit().assume_init();
    let mut buffer_1 =
        MaybeUninit::<[Mersenne31Quartic; MAX_SIZE_FOR_LEAF]>::uninit().assume_init();

    for round in 0..FOLDING_DEGREE_LOG2 {
        let roots_stride = 1 << round;
        if round > 0 {
            // we should remap evaluation points
            for i in 0..1 << (FOLDING_DEGREE_LOG2 - round - 1) {
                folding_evals_points_inversed
                    .get_unchecked_mut(i * roots_stride)
                    .square();
            }
        }
        let (input_buffer, output_buffer) = if round % 2 == 0 {
            (&mut buffer_0, &mut buffer_1)
        } else {
            (&mut buffer_1, &mut buffer_0)
        };
        let challenge = fri_folding_challenges_powers.get_unchecked(round);

        for i in 0..1 << (FOLDING_DEGREE_LOG2 - round - 1) {
            let root = folding_evals_points_inversed.get_unchecked(i * roots_stride);
            let (a, b) = if round == 0 {
                if core::mem::align_of::<Mersenne31Quartic>()
                    == core::mem::align_of::<Mersenne31Field>()
                {
                    // it's enough to cast
                    let a_ptr = leaf.as_ptr().add(2 * i * 4).cast::<Mersenne31Quartic>();
                    let b_ptr = a_ptr.add(1);

                    (a_ptr.as_ref_unchecked(), b_ptr.as_ref_unchecked())
                } else {
                    (
                        leaf_parsed.get_unchecked(2 * i),
                        leaf_parsed.get_unchecked(2 * i + 1),
                    )
                }
            } else {
                (
                    input_buffer.get_unchecked(2 * i),
                    input_buffer.get_unchecked(2 * i + 1),
                )
            };

            if Mersenne31Quartic::PREFER_FMA
                && Mersenne31Quartic::USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF
            {
                let mut folded = *a;
                folded.sub_assign(b);
                let root = Mersenne31Quartic::from_base(*root);
                let mut t = Mersenne31Quartic::ZERO;
                t.fused_mul_add_assign(&folded, &root);
                let mut folded = *a;
                folded.fused_mul_add_assign(&t, &challenge);
                folded.add_assign(&b);

                *output_buffer.get_unchecked_mut(i) = folded;
            } else {
                let mut folded = *a;
                folded.sub_assign(b);
                folded.mul_assign_by_base(root);
                folded.mul_assign(&challenge);
                folded.add_assign(a);
                folded.add_assign(b);

                *output_buffer.get_unchecked_mut(i) = folded;
            }
        }
    }

    *expected_value = if FOLDING_DEGREE_LOG2 % 2 == 0 {
        buffer_0[0]
    } else {
        buffer_1[0]
    };

    for _ in 0..FOLDING_DEGREE_LOG2 {
        evaluation_point.square();
        offset_inv.square();
    }

    *tree_index >>= FOLDING_DEGREE_LOG2;
    *domain_index = shared_bits_in_folding;
}

#[allow(invalid_value)]
pub unsafe fn fri_fold_by_log_n_with_fma<const FOLDING_DEGREE_LOG2: usize>(
    expected_value: &mut Mersenne31Quartic,
    evaluation_point: &mut Mersenne31Complex,
    domain_size_log_2: &mut usize,
    domain_index: &mut usize,
    tree_index: &mut usize,
    offset_inv: &mut Mersenne31Complex,
    leaf: &[Mersenne31Field],
    fri_folding_challenge: &Mersenne31Quartic,
    shared_factors_for_folding: &[Mersenne31Complex],
) {
    const MAX_SIZE_FOR_LEAF: usize = 32;
    const MAX_SIZE_FOR_ROOTS: usize = 16;

    // we will abuse FMA for pow
    assert!(Mersenne31Quartic::PREFER_FMA);
    assert!(Mersenne31Quartic::USE_SPEC_MUL_BY_BASE_VIA_MUL_BY_SELF);
    assert!(Mersenne31Quartic::CAN_PROJECT_FROM_BASE);

    assert!(FOLDING_DEGREE_LOG2 > 0);
    assert!(FOLDING_DEGREE_LOG2 <= 5);
    debug_assert_eq!(leaf.len(), (1 << FOLDING_DEGREE_LOG2) * 4);

    let in_leaf_mask: usize = (1 << FOLDING_DEGREE_LOG2) - 1;
    let eval_points_bits_mask = (1 << (*domain_size_log_2 - FOLDING_DEGREE_LOG2)) - 1;
    let generator_inv = Mersenne31Complex::TWO_ADICITY_GENERATORS_INVERSED[*domain_size_log_2];

    *domain_size_log_2 -= FOLDING_DEGREE_LOG2;

    let expected_index_in_rs_code_word_leaf = (*tree_index as usize) & in_leaf_mask;
    let value_at_expected_index = leaf
        .as_ptr()
        .add(expected_index_in_rs_code_word_leaf * 4)
        .cast::<[Mersenne31Field; 4]>();
    let value_at_expected_index =
        Mersenne31Quartic::project_ref_from_array(value_at_expected_index.as_ref_unchecked());
    // check that our simulated value is actually in the leaf
    assert!(*expected_value == *value_at_expected_index);

    // note that our evaluation points share highest N-3 bits, so we can just precompute additional multiplication
    // factors for lower bits. We only need elements that are not negations of each other

    let shared_bits_in_folding = *domain_index & eval_points_bits_mask;
    let generator_inv = Mersenne31Quartic::from_base(generator_inv);
    let mut evaluation_point_shared_factor =
        generator_inv.pow_with_fma(shared_bits_in_folding as u32);
    evaluation_point_shared_factor.mul_assign_by_base(&*offset_inv);
    // again - worst case size
    let mut folding_evals_points_inversed =
        MaybeUninit::<[Mersenne31Quartic; MAX_SIZE_FOR_ROOTS]>::uninit().assume_init();
    for i in 0..(1 << (FOLDING_DEGREE_LOG2 - 1)) {
        let mut t = evaluation_point_shared_factor;
        let shared_factor =
            Mersenne31Quartic::from_base(*shared_factors_for_folding.get_unchecked(i));
        t.mul_assign_with_fma(&shared_factor);
        t.mul_assign_with_fma(fri_folding_challenge);
        *folding_evals_points_inversed.get_unchecked_mut(i) = t;
    }

    let mut buffer_0 =
        MaybeUninit::<[Mersenne31Quartic; MAX_SIZE_FOR_LEAF]>::uninit().assume_init();
    let mut buffer_1 =
        MaybeUninit::<[Mersenne31Quartic; MAX_SIZE_FOR_LEAF]>::uninit().assume_init();

    for round in 0..FOLDING_DEGREE_LOG2 {
        // NOTE: we will only access roots at particular stride, but also we will only
        // access them in combination of challenge * root * other, so after we pre-multiplied those above,
        // we can just square only the needed roots and for free get squared challenges along with them

        let roots_stride = 1 << round;
        if round > 0 {
            // we should remap evaluation points
            for i in 0..1 << (FOLDING_DEGREE_LOG2 - round - 1) {
                folding_evals_points_inversed
                    .get_unchecked_mut(i * roots_stride)
                    .square_with_fma();
            }
        }
        let (input_buffer, output_buffer) = if round % 2 == 0 {
            (&mut buffer_0, &mut buffer_1)
        } else {
            (&mut buffer_1, &mut buffer_0)
        };

        for i in 0..1 << (FOLDING_DEGREE_LOG2 - round - 1) {
            let root = folding_evals_points_inversed.get_unchecked(i * roots_stride);
            let (a, b) = if round == 0 {
                assert!(Mersenne31Quartic::CAN_PROJECT_FROM_BASE);
                assert!(
                    core::mem::align_of::<Mersenne31Quartic>()
                        == core::mem::align_of::<Mersenne31Field>()
                );

                // it's enough to cast
                let a_ptr = leaf.as_ptr().add(2 * i * 4).cast::<Mersenne31Quartic>();
                let b_ptr = a_ptr.add(1);

                (a_ptr.as_ref_unchecked(), b_ptr.as_ref_unchecked())
            } else {
                (
                    input_buffer.get_unchecked(2 * i),
                    input_buffer.get_unchecked(2 * i + 1),
                )
            };

            // just use FMA for everything
            let mut folded = *b;
            folded.negate_self_and_add_other_with_fma(a);
            let mut t = *b;
            t.add_assign_with_fma(a);
            // root includes a challenge
            folded.fused_mul_add_assign(root, &t);
            *output_buffer.get_unchecked_mut(i) = folded;
        }
    }

    *expected_value = if FOLDING_DEGREE_LOG2 % 2 == 0 {
        buffer_0[0]
    } else {
        buffer_1[0]
    };

    for _ in 0..FOLDING_DEGREE_LOG2 {
        evaluation_point.square();
        offset_inv.square();
    }

    *tree_index >>= FOLDING_DEGREE_LOG2;
    *domain_index = shared_bits_in_folding;
}
