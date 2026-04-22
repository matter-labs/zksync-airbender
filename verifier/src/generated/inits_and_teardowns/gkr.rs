use super::common::{
    dot_eq, draw_field_els_into, draw_single_field_el, ext_from_nds, ext_from_raw_words,
    fold_standard_claims, make_eq_poly, read_field_el, read_reduced_field_el,
    verify_final_step_check, verify_sumcheck_rounds, EXT_DEGREE,
};
use super::constants::*;
use crate::prover::gkr::prover::GKRExternalChallenges;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{GKRVerifierOutput, LayerState};
use verifier_common::lazy_vec::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
use verifier_common::transcript::Blake2sTranscript;
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_0_compute_claim(
    output_claims: &[BabyBearExt4; 16usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 16usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
        (1usize, 8usize, 0usize),
        (1usize, 9usize, 0usize),
        (1usize, 10usize, 0usize),
        (1usize, 11usize, 0usize),
        (1usize, 12usize, 0usize),
        (1usize, 13usize, 0usize),
        (1usize, 14usize, 0usize),
        (1usize, 15usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_0_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (0usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (1usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (0usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(2usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(3usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(0usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(1usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (1usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(6usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(7usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(4usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(5usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (2usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (3usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (2usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(10usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(11usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(8usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(9usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (3usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(14usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(15usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(12usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(13usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (4usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (5usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (4usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(18usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(19usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(16usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(17usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (5usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(22usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(20usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(21usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (6usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (7usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (6usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(26usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(27usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(24usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(25usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (7usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(30usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(31usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(28usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(29usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (8usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (9usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (8usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(34usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(35usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(32usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(33usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (9usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(38usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(39usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(36usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(37usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (10usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (11usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (10usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(42usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(43usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(40usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(41usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (11usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(46usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(47usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(44usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (12usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (13usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (12usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(50usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(51usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(48usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(49usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (13usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(54usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(55usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(52usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(53usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (14usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (15usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (14usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(59usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(56usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(57usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                {
                    let mut t = linearization_challenges[0usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(64usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(65usize)[j];
                    let set_bits = (15usize as u32) << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_unchecked(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(60usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(61usize)[j]);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_1_compute_claim(
    output_claims: &[BabyBearExt4; 8usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 8usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_1_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 8usize] = [
            (2usize, [1usize, 3usize, 0usize, 0usize]),
            (2usize, [5usize, 7usize, 0usize, 0usize]),
            (2usize, [9usize, 11usize, 0usize, 0usize]),
            (2usize, [13usize, 15usize, 0usize, 0usize]),
            (2usize, [0usize, 2usize, 0usize, 0usize]),
            (2usize, [4usize, 6usize, 0usize, 0usize]),
            (2usize, [8usize, 10usize, 0usize, 0usize]),
            (2usize, [12usize, 14usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 8usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_2_compute_claim(
    output_claims: &[BabyBearExt4; 4usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 4usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_2_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 4usize] = [
            (2usize, [0usize, 1usize, 0usize, 0usize]),
            (2usize, [2usize, 3usize, 0usize, 0usize]),
            (2usize, [4usize, 5usize, 0usize, 0usize]),
            (2usize, [6usize, 7usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 4usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_3_compute_claim(
    output_claims: &[BabyBearExt4; 2usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 2usize] =
        [(1usize, 0usize, 0usize), (1usize, 1usize, 0usize)];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_3_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 2usize] = [
            (2usize, [0usize, 1usize, 0usize, 0usize]),
            (2usize, [2usize, 3usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 2usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                1usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                2usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                3usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                4usize => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                5usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        let mut num = bg;
                        field_ops::add_assign(&mut num, &dg);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                6usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let mut bg = evals.get_unchecked(idx[0])[j];
                        let mut dg = evals.get_unchecked(idx[2])[j];
                        let mut cb = evals.get_unchecked(idx[1])[j];
                        field_ops::add_assign(&mut bg, &lookup_additive_challenge);
                        field_ops::add_assign(&mut dg, &lookup_additive_challenge);
                        field_ops::mul_assign(&mut cb, &bg);
                        let mut num = dg;
                        field_ops::sub_assign(&mut num, &cb);
                        let mut den = bg;
                        field_ops::mul_assign(&mut den, &dg);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                7usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let mut r_g = evals.get_unchecked(idx[2])[j];
                        field_ops::add_assign(&mut r_g, &lookup_additive_challenge);
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &r_g);
                        field_ops::add_assign(&mut num, &b_val);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &r_g);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                8usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let b_val = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let d_val = evals.get_unchecked(idx[3])[j];
                        let mut num = a_val;
                        field_ops::mul_assign(&mut num, &d_val);
                        let mut cb_tmp = c_val;
                        field_ops::mul_assign(&mut cb_tmp, &b_val);
                        field_ops::add_assign(&mut num, &cb_tmp);
                        let mut den = b_val;
                        field_ops::mul_assign(&mut den, &d_val);
                        let out0 = num;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                9usize => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let a_val = evals.get_unchecked(idx[0])[j];
                        let mut b_cd = evals.get_unchecked(idx[1])[j];
                        let c_val = evals.get_unchecked(idx[2])[j];
                        let mut d_cd = evals.get_unchecked(idx[3])[j];
                        field_ops::add_assign(&mut b_cd, &lookup_additive_challenge);
                        field_ops::add_assign(&mut d_cd, &lookup_additive_challenge);
                        let mut ad_cd = a_val;
                        field_ops::mul_assign(&mut ad_cd, &d_cd);
                        let mut cb_cd = c_val;
                        field_ops::mul_assign(&mut cb_cd, &b_cd);
                        field_ops::sub_assign(&mut ad_cd, &cb_cd);
                        let mut den = b_cd;
                        field_ops::mul_assign(&mut den, &d_cd);
                        let out0 = ad_cd;
                        let out1 = den;
                        let mut c0 = bc0;
                        field_ops::mul_assign(&mut c0, &out0);
                        field_ops::add_assign(&mut acc[j], &c0);
                        let mut c1 = bc1;
                        field_ops::mul_assign(&mut c1, &out1);
                        field_ops::add_assign(&mut acc[j], &c1);
                    }
                }
                _ => unreachable!(),
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_unsafe)]
unsafe fn dim_reducing_compute_claim(
    output_claims: &[BabyBearExt4; 2usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = *output_claims.get_unchecked(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = *output_claims.get_unchecked(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    combined
}
#[inline(always)]
#[allow(unused_unsafe)]
unsafe fn dim_reducing_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
    indices: &[usize],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    let mut _idx = 0usize;
    {
        let si = unsafe { *indices.get_unchecked(_idx) };
        _idx += 1;
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let e2 = unsafe { *es.get_unchecked(2) };
        let e3 = unsafe { *es.get_unchecked(3) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        let mut c0 = bc;
        field_ops::mul_assign(&mut c0, &v01);
        field_ops::add_assign(&mut acc[0], &c0);
        let mut v23 = e2;
        field_ops::mul_assign(&mut v23, &e3);
        let mut c1 = bc;
        field_ops::mul_assign(&mut c1, &v23);
        field_ops::add_assign(&mut acc[1], &c1);
    }
    {
        let si = unsafe { *indices.get_unchecked(_idx) };
        _idx += 1;
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let e2 = unsafe { *es.get_unchecked(2) };
        let e3 = unsafe { *es.get_unchecked(3) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        let mut c0 = bc;
        field_ops::mul_assign(&mut c0, &v01);
        field_ops::add_assign(&mut acc[0], &c0);
        let mut v23 = e2;
        field_ops::mul_assign(&mut v23, &e3);
        let mut c1 = bc;
        field_ops::mul_assign(&mut c1, &v23);
        field_ops::add_assign(&mut acc[1], &c1);
    }
    acc
}
#[allow(unused_variables, unused_mut, unused_unsafe)]
pub(crate) fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    initial_transcript: &ConcreteInitialTranscript,
    ts: &mut ::verifier_common::structs::TranscriptState,
) -> Result<ConcreteGKRVerifierOutput, E::Error> {
    unsafe {
        let mut init_challenges = LazyVec::<BabyBearExt4, 2>::new();
        unsafe {
            init_challenges.set_len(2);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let address_high_bits_shift: u32 = 10u32;
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 32usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>());
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(32usize) };
        let mut all_challenges = LazyVec::<BabyBearExt4, { GKR_ROUNDS + 1 }>::new();
        unsafe {
            all_challenges.set_len(5usize);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, all_challenges.as_mut_slice());
        let batching_challenge = *all_challenges.get(5usize - 1);
        let mut eq_buf = LazyVec::<BabyBearExt4, 16usize>::new();
        let eq_challenges: &[BabyBearExt4; 4usize] = all_challenges.as_slice()[..4usize]
            .try_into()
            .unwrap_unchecked();
        make_eq_poly(eq_challenges, &mut eq_buf);
        let mut prev_claims: LazyVec<BabyBearExt4, GKR_ADDRS> = LazyVec::new();
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[0usize..16usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[16usize..32usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        let prev_point = {
            let mut lv = LazyVec::<BabyBearExt4, GKR_ROUNDS>::new();
            for i in 0..4usize {
                lv.push(*all_challenges.get(i));
            }
            unsafe {
                lv.set_len(GKR_ROUNDS);
            }
            unsafe { lv.into_array() }
        };
        let mut state = LayerState {
            prev_point,
            prev_point_len: 4usize,
            prev_claims,
            batching_challenge,
        };
        let mut eval_buf = CommitBuf::<GKR_EVAL_BUF>::new();
        const DIM_REDUCE_INDICES_4: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_5: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_6: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_7: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_8: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_9: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_10: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_11: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_12: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_13: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_14: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_15: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_16: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_17: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_18: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_19: [usize; 2usize] = [0usize, 1usize];
        const DIM_REDUCE_INDICES_20: [usize; 2usize] = [0usize, 1usize];
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 6usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                )?;
            let mut fc_len = 6usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_20,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    20usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 7usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                )?;
            let mut fc_len = 7usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_19,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    19usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 8usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                )?;
            let mut fc_len = 8usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_18,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    18usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 9usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                )?;
            let mut fc_len = 9usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_17,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    17usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 10usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                )?;
            let mut fc_len = 10usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_16,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    16usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 11usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                )?;
            let mut fc_len = 11usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_15,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    15usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 12usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                )?;
            let mut fc_len = 12usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_14,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    14usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 13usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                )?;
            let mut fc_len = 13usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_13,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    13usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 14usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                )?;
            let mut fc_len = 14usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_12,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    12usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 15usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                )?;
            let mut fc_len = 15usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_11,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    11usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 16usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                )?;
            let mut fc_len = 16usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_10,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    10usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 17usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                )?;
            let mut fc_len = 17usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_9,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    9usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 18usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                )?;
            let mut fc_len = 18usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_8,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    8usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_7,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    7usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 20usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_6,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    6usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_5,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    5usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 22usize;
            let data_words = 2usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(2usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_4,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    4usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_before_last = *draw_buf.get(0);
            let r_last = *draw_buf.get(1);
            let next_batching = *draw_buf.get(2);
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(2usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..2usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_3_compute_claim(
                state.prev_claims.as_array::<2usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 4usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(4usize);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    3usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<4usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_2_compute_claim(
                state.prev_claims.as_array::<4usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 8usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    2usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<8usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_1_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 16usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(16usize);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    1usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<16usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_0_compute_claim(
                state.prev_claims.as_array::<16usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 66usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(66usize);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    0usize,
                )?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<66usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        state.batching_challenge = draw_single_field_el(ts);
        let mut permutation_read_product: BabyBearExt4 = BabyBearExt4::ONE;
        let mut permutation_write_product: BabyBearExt4 = BabyBearExt4::ONE;
        {
            let mut read_product = BabyBearExt4::ONE;
            for i in 0..16usize {
                let eval = *evals_slice.get_unchecked(0usize + i);
                field_ops::mul_assign(&mut read_product, &eval);
            }
            let mut write_product = BabyBearExt4::ONE;
            for i in 0..16usize {
                let eval = *evals_slice.get_unchecked(16usize + i);
                field_ops::mul_assign(&mut write_product, &eval);
            }
            permutation_read_product = read_product;
            permutation_write_product = write_product;
        }
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            base_layer_addrs: LAYER_0_SORTED_ADDRS,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            permutation_read_product,
            permutation_write_product,
            additional_base_layer_openings: BASE_LAYER_ADDITIONAL_OPENINGS,
            whir_batching_challenge: state.batching_challenge,
        })
    }
}
pub struct VerifierImplementation;
impl
    ::verifier_common::ConcreteVerifierImpl<
        BabyBearField,
        BabyBearExt4,
        INIT_AND_TEARDOWN_SETS,
        EXTERNAL_CHALLENGES_FLATTENED_SIZE,
        CAP_SIZE,
        NUM_MEMORY_COMMITS,
        NUM_WITNESS_COMMITS,
        NUM_SETUP_COMMITS,
        PADDING_WORDS,
        GKR_ROUNDS,
        GKR_ADDRS,
    > for VerifierImplementation
{
    #[inline(always)]
    fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
        external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
    ) -> Result<ConcreteGKRVerifierOutput, E::Error> {
        verify_gkr::<I, E>(external_challenges, initial_transcript, transcript_state)
    }
    #[inline(always)]
    fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
        whir_batching_challenge: BabyBearExt4,
        base_layer_claims: &[BabyBearExt4],
        initial_claim_point: &[BabyBearExt4],
    ) -> Result<(), E::Error> {
        super::whir::verify_whir::<I, E>(
            initial_transcript,
            transcript_state,
            whir_batching_challenge,
            base_layer_claims,
            initial_claim_point,
        )
    }
}
