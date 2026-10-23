#![allow(
    dead_code,
    unused_imports,
    unused_unsafe,
    unused_assignments,
    clippy::needless_range_loop,
    clippy::too_many_arguments,
    clippy::manual_div_ceil,
    clippy::borrow_deref_ref,
    clippy::identity_op,
    clippy::missing_safety_doc,
    clippy::duplicate_mod,
    clippy::large_const_arrays
)]
use super::common::{
    dot_eq, draw_field_els_into, draw_field_els_into_after_pow, draw_fresh_field_els_into,
    draw_single_field_el, draw_single_field_el_after_pow, ext_from_nds, ext_from_raw_words,
    fold_standard_claims, make_eq_poly, read_field_el, read_reduced_field_el,
    verify_final_step_check, verify_sumcheck_rounds, EXT_DEGREE,
};
use super::constants::*;
use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::SimpleGateType;
use verifier_common::gkr::{GKRVerifierOutput, LayerState};
use verifier_common::lazy_vec::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
use verifier_common::whir::read_and_verify_pow;
use verifier_common::GKRExternalChallenges;
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_0_compute_claim(
    output_claims: &[BabyBearExt4; 77usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 61usize] = [
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
        (1usize, 16usize, 0usize),
        (1usize, 17usize, 0usize),
        (1usize, 18usize, 0usize),
        (1usize, 19usize, 0usize),
        (1usize, 20usize, 0usize),
        (1usize, 21usize, 0usize),
        (1usize, 22usize, 0usize),
        (1usize, 23usize, 0usize),
        (1usize, 24usize, 0usize),
        (1usize, 25usize, 0usize),
        (1usize, 26usize, 0usize),
        (1usize, 27usize, 0usize),
        (1usize, 28usize, 0usize),
        (1usize, 29usize, 0usize),
        (1usize, 30usize, 0usize),
        (1usize, 31usize, 0usize),
        (1usize, 32usize, 0usize),
        (1usize, 33usize, 0usize),
        (1usize, 34usize, 0usize),
        (1usize, 35usize, 0usize),
        (1usize, 36usize, 0usize),
        (1usize, 37usize, 0usize),
        (1usize, 38usize, 0usize),
        (1usize, 39usize, 0usize),
        (1usize, 40usize, 0usize),
        (1usize, 41usize, 0usize),
        (1usize, 42usize, 0usize),
        (1usize, 43usize, 0usize),
        (1usize, 44usize, 0usize),
        (1usize, 45usize, 0usize),
        (1usize, 46usize, 0usize),
        (1usize, 47usize, 0usize),
        (2usize, 48usize, 49usize),
        (2usize, 50usize, 51usize),
        (2usize, 52usize, 53usize),
        (2usize, 54usize, 55usize),
        (2usize, 56usize, 57usize),
        (2usize, 58usize, 59usize),
        (1usize, 60usize, 0usize),
        (2usize, 61usize, 62usize),
        (2usize, 63usize, 64usize),
        (2usize, 65usize, 66usize),
        (2usize, 67usize, 68usize),
        (1usize, 69usize, 0usize),
        (2usize, 70usize, 71usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_0_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(54usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(54usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(54usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(53usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(53usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(53usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(52usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(52usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(52usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(51usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(51usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(50usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(50usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(50usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(26usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(26usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(25usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(25usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(25usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(24usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(24usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(23usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(23usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(22usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(22usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(69usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(64usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(21usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(20usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(19usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(19usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(19usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(18usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(18usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(17usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(17usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(16usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(16usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(15usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(15usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(14usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(14usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(14usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(13usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(13usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(13usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(12usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(12usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(11usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(11usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(10usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(10usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(10usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(9usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(9usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(9usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(8usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(8usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(8usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(7usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(7usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(7usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(6usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(6usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(6usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(5usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(5usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(5usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val =
                    BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(2013233153u32));
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(77usize)[j],
                    &BabyBearField::from_reduced_raw_repr(2013257729u32),
                );
                field_ops::sub_assign(&mut val, &evals.get_unchecked(78usize)[j]);
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(81usize)[j],
                    &BabyBearField::from_reduced_raw_repr(8192u32),
                );
                field_ops::add_assign(&mut val, &evals.get_unchecked(82usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val =
                    BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(1509916673u32));
                {
                    let mut inner = evals.get_unchecked(77usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1981808641u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(81usize)[j],
                        &BabyBearField::from_reduced_raw_repr(62914560u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(77usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(81usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1981808641u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(81usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(77usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1761599489u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(81usize)[j],
                    &BabyBearField::from_reduced_raw_repr(251666432u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(5usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(6usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(7usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(8usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(9usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(10usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(13usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(14usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(19usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(5usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(6usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(7usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(8usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(9usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(10usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(11usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(12usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(13usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(14usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(15usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(16usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(17usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(18usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(19usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(20usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(21usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(64usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(69usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                field_ops::sub_assign(&mut val, &evals.get_unchecked(5usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(6usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(7usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(8usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(9usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(10usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(11usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(12usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(13usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(14usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(15usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(16usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(17usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(18usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(20usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(21usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(64usize)[j]);
                field_ops::sub_assign(&mut val, &evals.get_unchecked(69usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(74usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(51usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(76usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(74usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(79usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(79usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(79usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(51usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(79usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(51usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(75usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(79usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(74usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(15usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524105u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(16usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524105u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(17usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524105u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(18usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524105u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(74usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1073741816u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(25usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(26usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(25usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(26usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(44usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(70usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(25usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(26usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(44usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(65usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(63usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(50usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(63usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(73usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(73usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(62usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(50usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(62usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(72usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(72usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(24usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(50usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(24usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(24usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(28usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(71usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(28usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(66usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(27usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(70usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(27usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(65usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(22usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(69usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(23usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(59usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(66usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(71usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(69usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(22usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(69usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(58usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(65usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(70usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(71usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(71usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(69usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(1usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(70usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(1usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(70usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(66usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(66usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(64usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(0usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(65usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(0usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(65usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(31usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(34usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(35usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(38usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(39usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(42usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(43usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(31usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(33usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(34usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(36usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(37usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(40usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(43usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(29usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(32usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(33usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(36usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(37usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(40usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(41usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(29usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(32usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(35usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(38usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(39usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(41usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(42usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268434910u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(73usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(19usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(72usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(19usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(73usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(19usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(19usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(49usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(26usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(15usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(16usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(49usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(25usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(25usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(59usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(25usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(25usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(80usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(15usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(16usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(49usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(34usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(34usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(34usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(34usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(17usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1073741816u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(18usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1073741816u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(49usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524105u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(49usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(17usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(17usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(23usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(23usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(23usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(59usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(23usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(59usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(17usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(15usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1073741816u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(16usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1073741816u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(73usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(72usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(61usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(60usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(63usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(62usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(12usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(5usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(7usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(59usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(5usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(59usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(6usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(76usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(7usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(8usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(9usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(10usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(23usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(24usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(25usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(59usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(68usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(73usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(14usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(8usize)[j],
                    &BabyBearField::from_reduced_raw_repr(2013200385u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(9usize)[j],
                    &BabyBearField::from_reduced_raw_repr(2013200385u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(10usize)[j],
                    &BabyBearField::from_reduced_raw_repr(2013200385u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(11usize)[j],
                    &BabyBearField::from_reduced_raw_repr(2013200385u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(5usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(7usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(5usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(6usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(75usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(7usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(8usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(9usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(10usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(44usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(24usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(58usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(67usize)[j]);
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(14usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(8usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(9usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(10usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(11usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(8usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(9usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(10usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(22usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(8usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(9usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(10usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(11usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(58usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(59usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::sub_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(63usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(73usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(8usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(58usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(59usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1744970275u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(62usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(63usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(73usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(9usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(48usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(73usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(10usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(48usize)[j];
                    field_ops::negate(&mut inner);
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(72usize)[j]);
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(73usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(67usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(68usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(11usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(62usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(63usize)[j],
                        &BabyBearField::from_reduced_raw_repr(65536u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(58usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(62usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(65536u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(63usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(59usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(48usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(74usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(74usize)[j],
                    );
                }
                field_ops::sub_assign(&mut val, &evals.get_unchecked(74usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 13usize] = [
            (
                SimpleGateType::LookupWithSetup,
                [44usize, 55usize, 91usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [45usize, 72usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [73usize, 76usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [34usize, 65usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [66usize, 70usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [71usize, 79usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [80usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [81usize, 56usize, 92usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [82usize, 103usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [104usize, 105usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [106usize, 107usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [108usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupInitialWithCachedDenominators,
                [74usize, 109usize, 57usize, 110usize],
            ),
        ];
        let mut _sg = 13usize;
        while _sg > 0 {
            _sg -= 1;
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::Product => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::UnbalancedProduct => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupWithSetup => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupUnbalanced => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupAggregatePair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(43usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(42usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(41usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(43usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(40usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(42usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(41usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(79usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(79usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(79usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(79usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(40usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(26usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(59usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(47usize)[j],
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(63usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(34usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(34usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(34usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(34usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(59usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(805306362u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(15usize)[j],
                    &BabyBearField::from_reduced_raw_repr(536870908u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(16usize)[j],
                    &BabyBearField::from_reduced_raw_repr(536870908u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(17usize)[j],
                    &BabyBearField::from_reduced_raw_repr(536870908u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(18usize)[j],
                    &BabyBearField::from_reduced_raw_repr(536870908u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(402653165u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(39usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(38usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(37usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(39usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(36usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(38usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(37usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(36usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(47usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(15usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(16usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(17usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(18usize)[j],
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(27usize)[j],
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(28usize)[j],
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(31usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(27usize)[j],
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(28usize)[j],
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(31usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(27usize)[j],
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(28usize)[j],
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(31usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(23usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(27usize)[j],
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(28usize)[j],
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(31usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(45usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(536870908u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(15usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1610612628u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(16usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1610612628u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(17usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1610612628u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(18usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1610612628u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(402653165u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(35usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(34usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(33usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(35usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(32usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(34usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(33usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(32usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(31usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(31usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(31usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(31usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(58usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(46usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(62usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(58usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(20usize)[j]);
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(15usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(16usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(17usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(18usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(402653165u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(31usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(31usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(30usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(29usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(20usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(2usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(28usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(46usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(59usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(59usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(59usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(59usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(4usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(15usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(16usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(17usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(18usize)[j],
                    &BabyBearField::from_reduced_raw_repr(1342177270u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(402653165u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(50usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(73usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(46usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1996488705u32),
                    );
                    field_ops::add_assign_product_with_base(
                        &mut inner,
                        &evals.get_unchecked(62usize)[j],
                        &BabyBearField::from_reduced_raw_repr(16777216u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(27usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(21usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(50usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(72usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(21usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(3usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(15usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(16usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(17usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(44usize)[j];
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(45usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(18usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(46usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(20usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(50usize)[j];
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(27usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(50usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(28usize)[j],
                    );
                }
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(50usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(1073741752u32),
                    );
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(74usize)[j],
                    );
                }
                field_ops::add_assign(&mut val, &evals.get_unchecked(15usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(16usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(17usize)[j]);
                field_ops::add_assign(&mut val, &evals.get_unchecked(18usize)[j]);
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(20usize)[j],
                    &BabyBearField::from_reduced_raw_repr(134217711u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(21usize)[j],
                    &BabyBearField::from_reduced_raw_repr(805306362u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let val = {
                let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(28usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(64usize)[j],
                    );
                }
                {
                    let mut inner = evals.get_unchecked(24usize)[j];
                    field_ops::mul_assign_by_base(
                        &mut inner,
                        &BabyBearField::from_reduced_raw_repr(268295646u32),
                    );
                    field_ops::add_assign(&mut inner, &evals.get_unchecked(28usize)[j]);
                    field_ops::add_assign_product(
                        &mut val,
                        &inner,
                        &evals.get_unchecked(69usize)[j],
                    );
                }
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(64usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524233u32),
                );
                field_ops::add_assign_product_with_base(
                    &mut val,
                    &evals.get_unchecked(69usize)[j],
                    &BabyBearField::from_reduced_raw_repr(939524233u32),
                );
                val
            };
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                let ram_constant_el = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut result, &ram_constant_el);
                {
                    let mut t = linearization_challenges[0usize];
                    let base = evals.get_unchecked(93usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(94usize)[j];
                    let set_bits = inits_and_teardowns_top_bits[0usize] << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_with_reduction(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    let base = evals.get_unchecked(85usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    let base = evals.get_unchecked(86usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    let base = evals.get_unchecked(83usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    let base = evals.get_unchecked(84usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                let ram_constant_el = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut result, &ram_constant_el);
                {
                    let mut t = linearization_challenges[0usize];
                    let base = evals.get_unchecked(93usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(94usize)[j];
                    let set_bits = inits_and_teardowns_top_bits[1usize] << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_with_reduction(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[2usize];
                    let base = evals.get_unchecked(89usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[3usize];
                    let base = evals.get_unchecked(90usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[4usize];
                    let base = evals.get_unchecked(87usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[5usize];
                    let base = evals.get_unchecked(88usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        for j in 0..1 {
            let mut lhs = {
                let mut result = permutation_argument_additive_part;
                let ram_constant_el = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut result, &ram_constant_el);
                {
                    let mut t = linearization_challenges[0usize];
                    let base = evals.get_unchecked(93usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(94usize)[j];
                    let set_bits = inits_and_teardowns_top_bits[0usize] << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_with_reduction(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            let mut rhs = {
                let mut result = permutation_argument_additive_part;
                let ram_constant_el = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut result, &ram_constant_el);
                {
                    let mut t = linearization_challenges[0usize];
                    let base = evals.get_unchecked(93usize)[j];
                    field_ops::mul_assign_by_base(&mut t, &base);
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = linearization_challenges[1usize];
                    let mut addr_hi = evals.get_unchecked(94usize)[j];
                    let set_bits = inits_and_teardowns_top_bits[1usize] << address_high_bits_shift;
                    if set_bits != 0 {
                        let set_field = BabyBearField::from_u32_with_reduction(set_bits);
                        field_ops::add_assign_base(&mut addr_hi, &set_field);
                    }
                    field_ops::mul_assign_by_base(&mut t, &addr_hi);
                    field_ops::add_assign(&mut result, &t);
                }
                result
            };
            field_ops::mul_assign(&mut lhs, &rhs);
            let val = lhs;
            {
                let mut h = val;
                field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                acc[j] = h;
            }
        }
    }
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 5usize] = [
            (SimpleGateType::Copy, [74usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [95usize, 96usize, 0usize, 0usize]),
            (SimpleGateType::Product, [97usize, 98usize, 0usize, 0usize]),
            (SimpleGateType::Product, [99usize, 100usize, 0usize, 0usize]),
            (
                SimpleGateType::Product,
                [101usize, 102usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 5usize;
        while _sg > 0 {
            _sg -= 1;
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::Product => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::UnbalancedProduct => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupWithSetup => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupUnbalanced => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupAggregatePair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
            }
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_1_compute_claim(
    output_claims: &[BabyBearExt4; 25usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 16usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (2usize, 3usize, 4usize),
        (2usize, 5usize, 6usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (2usize, 11usize, 12usize),
        (2usize, 13usize, 14usize),
        (1usize, 15usize, 0usize),
        (1usize, 16usize, 0usize),
        (2usize, 17usize, 18usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (1usize, 23usize, 0usize),
        (1usize, 24usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_1_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 16usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 3usize, 0usize, 0usize]),
            (SimpleGateType::Product, [2usize, 4usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [18usize, 19usize, 20usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [16usize, 17usize, 14usize, 15usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [12usize, 13usize, 10usize, 11usize],
            ),
            (
                SimpleGateType::LookupUnbalanced,
                [8usize, 9usize, 7usize, 0usize],
            ),
            (
                SimpleGateType::LookupUnbalanced,
                [27usize, 28usize, 29usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [25usize, 26usize, 23usize, 24usize],
            ),
            (SimpleGateType::Copy, [21usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [22usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupInitialPair,
                [32usize, 33usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [34usize, 35usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupUnbalanced,
                [30usize, 31usize, 36usize, 0usize],
            ),
            (SimpleGateType::Copy, [6usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [5usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 16usize;
        while _sg > 0 {
            _sg -= 1;
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::Product => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::UnbalancedProduct => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupWithSetup => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupUnbalanced => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupAggregatePair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
            }
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_2_compute_claim(
    output_claims: &[BabyBearExt4; 16usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 12usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (2usize, 6usize, 7usize),
        (1usize, 8usize, 0usize),
        (1usize, 9usize, 0usize),
        (2usize, 10usize, 11usize),
        (1usize, 12usize, 0usize),
        (1usize, 13usize, 0usize),
        (1usize, 14usize, 0usize),
        (1usize, 15usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_2_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 12usize] = [
            (
                SimpleGateType::MaskToIdentity,
                [1usize, 0usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::MaskToIdentity,
                [2usize, 0usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [9usize, 10usize, 7usize, 8usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [5usize, 6usize, 3usize, 4usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [15usize, 16usize, 13usize, 14usize],
            ),
            (SimpleGateType::Copy, [11usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [12usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [21usize, 22usize, 19usize, 20usize],
            ),
            (SimpleGateType::Copy, [17usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [18usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [23usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [24usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 12usize;
        while _sg > 0 {
            _sg -= 1;
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::Product => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::UnbalancedProduct => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupWithSetup => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupUnbalanced => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupAggregatePair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
            }
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_3_compute_claim(
    output_claims: &[BabyBearExt4; 10usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 7usize] = [
        (2usize, 0usize, 1usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
        (1usize, 8usize, 0usize),
        (1usize, 9usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_3_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 7usize] = [
            (
                SimpleGateType::LookupAggregatePair,
                [4usize, 5usize, 2usize, 3usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [8usize, 9usize, 6usize, 7usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [12usize, 13usize, 10usize, 11usize],
            ),
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [1usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [14usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [15usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 7usize;
        while _sg > 0 {
            _sg -= 1;
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::Product => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let mask_val = evals.get_unchecked(idx[1])[j];
                        field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
                        field_ops::mul_assign(&mut val, &mask_val);
                        field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::UnbalancedProduct => {
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        {
                            let mut h = val;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupWithSetup => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupUnbalanced => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupAggregatePair => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    for j in 0..1 {
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
                        {
                            let mut h = out1;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                        {
                            let mut h = out0;
                            field_ops::add_assign_product(&mut h, &acc[j], &batch_base);
                            acc[j] = h;
                        }
                    }
                }
            }
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_unsafe)]
unsafe fn dim_reducing_compute_claim(
    output_claims: &[BabyBearExt4; 10usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut combined = *output_claims.get_unchecked(9usize);
    {
        let mut h = *output_claims.get_unchecked(8usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(7usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(6usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(5usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(4usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(3usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(2usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(1usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    {
        let mut h = *output_claims.get_unchecked(0usize);
        field_ops::add_assign_product(&mut h, &combined, &batch_base);
        combined = h;
    }
    combined
}
#[inline(always)]
#[allow(unused_unsafe)]
unsafe fn dim_reducing_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    indices: &[usize],
) -> BabyBearExt4 {
    let mut acc = BabyBearExt4::ZERO;
    {
        let si = unsafe { *indices.get_unchecked(9usize) };
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        acc = v01;
    }
    {
        let si = unsafe { *indices.get_unchecked(8usize) };
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        {
            let mut h = v01;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
    }
    {
        let si0 = unsafe { *indices.get_unchecked(6usize) };
        let si1 = unsafe { *indices.get_unchecked(7usize) };
        let v0 = unsafe { evals.get_unchecked(si0) };
        let v1 = unsafe { evals.get_unchecked(si1) };
        let v0a = unsafe { *v0.get_unchecked(0) };
        let v0b = unsafe { *v0.get_unchecked(1) };
        let v1a = unsafe { *v1.get_unchecked(0) };
        let v1b = unsafe { *v1.get_unchecked(1) };
        let mut num = v0a;
        field_ops::mul_assign(&mut num, &v1b);
        let mut cb_tmp = v0b;
        field_ops::mul_assign(&mut cb_tmp, &v1a);
        field_ops::add_assign(&mut num, &cb_tmp);
        let mut den = v1a;
        field_ops::mul_assign(&mut den, &v1b);
        {
            let mut h = den;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
        {
            let mut h = num;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
    }
    {
        let si0 = unsafe { *indices.get_unchecked(4usize) };
        let si1 = unsafe { *indices.get_unchecked(5usize) };
        let v0 = unsafe { evals.get_unchecked(si0) };
        let v1 = unsafe { evals.get_unchecked(si1) };
        let v0a = unsafe { *v0.get_unchecked(0) };
        let v0b = unsafe { *v0.get_unchecked(1) };
        let v1a = unsafe { *v1.get_unchecked(0) };
        let v1b = unsafe { *v1.get_unchecked(1) };
        let mut num = v0a;
        field_ops::mul_assign(&mut num, &v1b);
        let mut cb_tmp = v0b;
        field_ops::mul_assign(&mut cb_tmp, &v1a);
        field_ops::add_assign(&mut num, &cb_tmp);
        let mut den = v1a;
        field_ops::mul_assign(&mut den, &v1b);
        {
            let mut h = den;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
        {
            let mut h = num;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
    }
    {
        let si0 = unsafe { *indices.get_unchecked(2usize) };
        let si1 = unsafe { *indices.get_unchecked(3usize) };
        let v0 = unsafe { evals.get_unchecked(si0) };
        let v1 = unsafe { evals.get_unchecked(si1) };
        let v0a = unsafe { *v0.get_unchecked(0) };
        let v0b = unsafe { *v0.get_unchecked(1) };
        let v1a = unsafe { *v1.get_unchecked(0) };
        let v1b = unsafe { *v1.get_unchecked(1) };
        let mut num = v0a;
        field_ops::mul_assign(&mut num, &v1b);
        let mut cb_tmp = v0b;
        field_ops::mul_assign(&mut cb_tmp, &v1a);
        field_ops::add_assign(&mut num, &cb_tmp);
        let mut den = v1a;
        field_ops::mul_assign(&mut den, &v1b);
        {
            let mut h = den;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
        {
            let mut h = num;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
    }
    {
        let si = unsafe { *indices.get_unchecked(1usize) };
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        {
            let mut h = v01;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
    }
    {
        let si = unsafe { *indices.get_unchecked(0usize) };
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        {
            let mut h = v01;
            field_ops::add_assign_product(&mut h, &acc, &batch_base);
            acc = h;
        }
    }
    acc
}
#[doc = " Closed-form eval of VirtualSetup(RangeCheck16Bits) at `state.prev_point` (lower 16 bits free, top bits forced to zero)."]
#[doc = " Source: prover/src/gkr/virtual_polys/range_check.rs."]
#[doc = " The `prev_claims` index is the position assigned to this VirtualSetup poly by the"]
#[doc = " canonical layer-0 layout (memory cols → witness cols → setup cols → virtual setups → others)."]
#[inline(always)]
fn check_virtual_setup_range_check_16bits<E: ErrorCreator>(
    state: &LayerState<BabyBearExt4, CLAIM_POINT_CAPACITY, GKR_ADDRS>,
) -> Result<(), E::Error> {
    unsafe {
        let pt = state.prev_point.get_unchecked(..23usize);
        let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
        let mut prefactor: BabyBearField = BabyBearField::ONE;
        let mut k: usize = 0;
        while k < 16usize {
            let mut t = *pt.get_unchecked(k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 23usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(106usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(106usize));
        }
    }
    Ok(())
}
#[doc = " Closed-form eval of VirtualSetup(RangeCheckTimestamp) at `state.prev_point` (lower 19 bits free, top bits forced to zero)."]
#[doc = " Source: prover/src/gkr/virtual_polys/range_check.rs."]
#[doc = " The `prev_claims` index is the position assigned to this VirtualSetup poly by the"]
#[doc = " canonical layer-0 layout (memory cols → witness cols → setup cols → virtual setups → others)."]
#[inline(always)]
fn check_virtual_setup_range_check_timestamp<E: ErrorCreator>(
    state: &LayerState<BabyBearExt4, CLAIM_POINT_CAPACITY, GKR_ADDRS>,
) -> Result<(), E::Error> {
    unsafe {
        let pt = state.prev_point.get_unchecked(..23usize);
        let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
        let mut prefactor: BabyBearField = BabyBearField::ONE;
        let mut k: usize = 0;
        while k < 19usize {
            let mut t = *pt.get_unchecked(k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 23usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(107usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(107usize));
        }
    }
    Ok(())
}
#[doc = " Closed-form eval of VirtualSetup(InitsAndTeardownsLow/High) at `state.prev_point`."]
#[doc = " Low half = bits [2..16) of the address (top 2 bits zeroed); high half = the high 9 address bits."]
#[doc = " Source: prover/src/gkr/virtual_polys/init_and_teardown_base.rs."]
#[doc = " The `prev_claims` indices are positions assigned by the canonical layer-0 layout"]
#[doc = " (memory cols → witness cols → setup cols → virtual setups → others)`."]
#[inline(always)]
fn check_virtual_setup_inits_and_teardowns<E: ErrorCreator>(
    state: &LayerState<BabyBearExt4, CLAIM_POINT_CAPACITY, GKR_ADDRS>,
) -> Result<(), E::Error> {
    unsafe {
        let pt = state.prev_point.get_unchecked(..23usize);
        let mut low_eval: BabyBearExt4 = BabyBearExt4::ZERO;
        {
            let mut prefactor: BabyBearField = BabyBearField::ONE;
            let mut wb: usize = 0;
            while wb < 2usize {
                field_ops::double(&mut prefactor);
                wb += 1;
            }
            let mut k: usize = 0;
            while k < 14usize {
                let mut t = *pt.get_unchecked(k);
                field_ops::mul_assign_by_base(&mut t, &prefactor);
                field_ops::add_assign(&mut low_eval, &t);
                field_ops::double(&mut prefactor);
                k += 1;
            }
        }
        let mut high_eval: BabyBearExt4 = BabyBearExt4::ZERO;
        {
            let mut prefactor: BabyBearField = BabyBearField::ONE;
            let mut k: usize = 0;
            while k < 23usize - 14usize {
                let mut t = *pt.get_unchecked(14usize + k);
                field_ops::mul_assign_by_base(&mut t, &prefactor);
                field_ops::add_assign(&mut high_eval, &t);
                field_ops::double(&mut prefactor);
                k += 1;
            }
        }
        if low_eval != *state.prev_claims.get_unchecked(108usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(108usize));
        }
        if high_eval != *state.prev_claims.get_unchecked(109usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(109usize));
        }
    }
    Ok(())
}
#[allow(unused_variables, unused_mut, unused_unsafe)]
pub(crate) fn verify_gkr<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    initial_transcript: &ConcreteInitialTranscript,
    ts: &mut ::verifier_common::structs::TranscriptState,
    nd_source: &mut I,
) -> Result<ConcreteGKRVerifierOutput, E::Error> {
    unsafe {
        let mut init_challenges = LazyVec::<BabyBearExt4, 2>::new();
        unsafe {
            init_challenges.set_len(2);
        }
        read_and_verify_pow::<I>(ts, LOOKUP_CHALLENGES_POW_BITS, nd_source);
        draw_field_els_into_after_pow::<DRAW_BUF_CAPACITY>(ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let address_high_bits_shift: u32 = 9u32;
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 160usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf
                    .data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(160usize) };
        let mut all_challenges = LazyVec::<BabyBearExt4, { CLAIM_POINT_CAPACITY + 1 }>::new();
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
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[32usize..48usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[48usize..64usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[64usize..80usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[80usize..96usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] =
                evals_slice[96usize..112usize].try_into().unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] = evals_slice[112usize..128usize]
                .try_into()
                .unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] = evals_slice[128usize..144usize]
                .try_into()
                .unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        {
            let vals: &[BabyBearExt4; 16usize] = evals_slice[144usize..160usize]
                .try_into()
                .unwrap_unchecked();
            let eq_arr: &[BabyBearExt4; 16usize] = eq_buf.as_slice().try_into().unwrap_unchecked();
            let claim = dot_eq(vals, eq_arr);
            prev_claims.push(claim);
        }
        let prev_point = {
            let mut lv = LazyVec::<BabyBearExt4, CLAIM_POINT_CAPACITY>::new();
            for i in 0..4usize {
                lv.push(*all_challenges.get(i));
            }
            unsafe {
                lv.set_len(CLAIM_POINT_CAPACITY);
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
        const DIM_REDUCE_INDICES_4: [usize; 10usize] = [
            6usize, 7usize, 0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_5: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_6: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_7: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_8: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_9: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_10: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_11: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_12: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_13: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_14: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_15: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_16: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_17: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_18: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_19: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_20: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_21: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        const DIM_REDUCE_INDICES_22: [usize; 10usize] = [
            0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
        ];
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log("GKR COMPRESSION INIT");
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 4usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                    nd_source,
                )?;
            let mut fc_len = 4usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_22,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 22usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 22");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 5usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                    nd_source,
                )?;
            let mut fc_len = 5usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_21,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 21usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 21");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 6usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                    nd_source,
                )?;
            let mut fc_len = 6usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_20,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 20usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 20");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 7usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                    nd_source,
                )?;
            let mut fc_len = 7usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_19,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 19usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 19");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 8usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                    nd_source,
                )?;
            let mut fc_len = 8usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_18,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 18usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 18");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 9usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                    nd_source,
                )?;
            let mut fc_len = 9usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_17,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 17usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 17");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 10usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                    nd_source,
                )?;
            let mut fc_len = 10usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_16,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 16usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 16");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 11usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                    nd_source,
                )?;
            let mut fc_len = 11usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_15,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 15usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 15");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 12usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                    nd_source,
                )?;
            let mut fc_len = 12usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_14,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 14usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 14");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 13usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                    nd_source,
                )?;
            let mut fc_len = 13usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_13,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 13usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 13");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 14usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                    nd_source,
                )?;
            let mut fc_len = 14usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_12,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 12usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 12");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 15usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                    nd_source,
                )?;
            let mut fc_len = 15usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_11,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 11usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 11");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 16usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                    nd_source,
                )?;
            let mut fc_len = 16usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_10,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 10usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 10");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 17usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                    nd_source,
                )?;
            let mut fc_len = 17usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_9,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 9usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 9");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 18usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                    nd_source,
                )?;
            let mut fc_len = 18usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_8,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 8usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 8");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_7,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 7usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 7");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                    nd_source,
                )?;
            let mut fc_len = 20usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_6,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 6usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 6");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                    nd_source,
                )?;
            let mut fc_len = 21usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_5,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 5usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 5");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                    nd_source,
                )?;
            let mut fc_len = 22usize;
            let data_words = 10usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(10usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_4,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 4usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(10usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..10usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 4");
        }
        {
            let initial_claim = layer_3_compute_claim(
                state.prev_claims.as_array::<10usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                    nd_source,
                )?;
            let fc_len = 23usize;
            const NUM_AT_POINT_EVALS: usize = 16usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 3usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<16usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 3");
        }
        {
            let initial_claim = layer_2_compute_claim(
                state.prev_claims.as_array::<16usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                    nd_source,
                )?;
            let fc_len = 23usize;
            const NUM_AT_POINT_EVALS: usize = 25usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 2usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<25usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 2");
        }
        {
            let initial_claim = layer_1_compute_claim(
                state.prev_claims.as_array::<25usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                    nd_source,
                )?;
            let fc_len = 23usize;
            const NUM_AT_POINT_EVALS: usize = 37usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 1usize)?;
            }
            const NUM_EXTRA_EVALS: usize = 40usize;
            {
                let mut i = 0;
                while i < NUM_EXTRA_EVALS * EXT_DEGREE {
                    eval_buf.data_write(
                        data_words + i,
                        read_reduced_field_el::<I>(nd_source).as_u32_raw_repr(),
                    );
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, NUM_EXTRA_EVALS>::new();
            {
                let slice: &[BabyBearExt4] =
                    unsafe { eval_buf.data_as(NUM_AT_POINT_EVALS + NUM_EXTRA_EVALS) };
                let mut k = NUM_AT_POINT_EVALS;
                while k < NUM_AT_POINT_EVALS + NUM_EXTRA_EVALS {
                    extra_evals.push(unsafe { *slice.get_unchecked(k) });
                    k += 1;
                }
            }
            ts.commit(&mut eval_buf, data_words + NUM_EXTRA_EVALS * EXT_DEGREE);
            let next_batching = draw_single_field_el(ts);
            let final_step_evals: &[[BabyBearExt4; 1]] =
                unsafe { eval_buf.data_as(NUM_AT_POINT_EVALS) };
            state.prev_claims.clear();
            {
                const EXTRA_POS: [(usize, usize); 40usize] = [
                    (8usize, 0usize),
                    (9usize, 1usize),
                    (10usize, 2usize),
                    (11usize, 3usize),
                    (12usize, 4usize),
                    (13usize, 5usize),
                    (14usize, 6usize),
                    (15usize, 7usize),
                    (16usize, 8usize),
                    (17usize, 9usize),
                    (18usize, 10usize),
                    (19usize, 11usize),
                    (20usize, 12usize),
                    (21usize, 13usize),
                    (22usize, 14usize),
                    (23usize, 15usize),
                    (24usize, 16usize),
                    (25usize, 17usize),
                    (26usize, 18usize),
                    (27usize, 19usize),
                    (28usize, 20usize),
                    (29usize, 21usize),
                    (30usize, 22usize),
                    (31usize, 23usize),
                    (32usize, 24usize),
                    (33usize, 25usize),
                    (34usize, 26usize),
                    (35usize, 27usize),
                    (36usize, 28usize),
                    (37usize, 29usize),
                    (38usize, 30usize),
                    (39usize, 31usize),
                    (40usize, 32usize),
                    (41usize, 33usize),
                    (42usize, 34usize),
                    (43usize, 35usize),
                    (44usize, 36usize),
                    (45usize, 37usize),
                    (46usize, 38usize),
                    (47usize, 39usize),
                ];
                let mut regular_idx: usize = 0;
                let mut ep_idx: usize = 0;
                let mut merged_idx: usize = 0;
                while merged_idx < 77usize {
                    if ep_idx < 40usize && EXTRA_POS[ep_idx].0 == merged_idx {
                        state
                            .prev_claims
                            .push(*extra_evals.get(EXTRA_POS[ep_idx].1));
                        ep_idx += 1;
                    } else {
                        state
                            .prev_claims
                            .push(final_step_evals.get_unchecked(regular_idx)[0]);
                        regular_idx += 1;
                    }
                    merged_idx += 1;
                }
            }
            {
                const VL_DESCS: [(usize, usize, usize); 5usize] = [
                    (72usize, 0usize, 10usize),
                    (73usize, 10usize, 10usize),
                    (74usize, 20usize, 10usize),
                    (75usize, 30usize, 10usize),
                    (76usize, 40usize, 10usize),
                ];
                const VL_COLS: [(u32, usize, usize); 50usize] = [
                    (0u32, 0usize, 1usize),
                    (0u32, 1usize, 1usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 0usize),
                    (0u32, 3usize, 0usize),
                    (0u32, 3usize, 0usize),
                    (0u32, 3usize, 0usize),
                    (0u32, 3usize, 0usize),
                    (0u32, 3usize, 0usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (0u32, 8usize, 1usize),
                    (0u32, 9usize, 1usize),
                    (0u32, 10usize, 1usize),
                    (0u32, 11usize, 1usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 1usize),
                    (0u32, 13usize, 1usize),
                    (0u32, 14usize, 1usize),
                    (0u32, 15usize, 1usize),
                    (0u32, 16usize, 1usize),
                    (0u32, 17usize, 1usize),
                    (0u32, 18usize, 1usize),
                    (0u32, 19usize, 1usize),
                    (0u32, 20usize, 1usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 1usize),
                    (0u32, 22usize, 1usize),
                    (0u32, 23usize, 1usize),
                    (0u32, 24usize, 1usize),
                    (0u32, 25usize, 1usize),
                    (0u32, 26usize, 1usize),
                    (0u32, 27usize, 1usize),
                    (0u32, 28usize, 1usize),
                    (0u32, 29usize, 1usize),
                    (0u32, 30usize, 0usize),
                    (0u32, 30usize, 1usize),
                    (0u32, 31usize, 1usize),
                    (0u32, 32usize, 1usize),
                    (0u32, 33usize, 1usize),
                    (0u32, 34usize, 1usize),
                    (0u32, 35usize, 1usize),
                    (0u32, 36usize, 1usize),
                    (0u32, 37usize, 1usize),
                    (0u32, 38usize, 1usize),
                    (0u32, 39usize, 0usize),
                    (0u32, 39usize, 1usize),
                ];
                const VL_TERMS: [(u32, usize); 40usize] = [
                    (268435454u32, 9usize),
                    (268435454u32, 10usize),
                    (268435454u32, 11usize),
                    (268435454u32, 8usize),
                    (268435454u32, 13usize),
                    (268435454u32, 14usize),
                    (268435454u32, 15usize),
                    (268435454u32, 16usize),
                    (268435454u32, 17usize),
                    (268435454u32, 18usize),
                    (268435454u32, 19usize),
                    (268435454u32, 20usize),
                    (268435454u32, 12usize),
                    (268435454u32, 22usize),
                    (268435454u32, 23usize),
                    (268435454u32, 24usize),
                    (268435454u32, 25usize),
                    (268435454u32, 26usize),
                    (268435454u32, 27usize),
                    (268435454u32, 28usize),
                    (268435454u32, 29usize),
                    (268435454u32, 21usize),
                    (268435454u32, 31usize),
                    (268435454u32, 32usize),
                    (268435454u32, 33usize),
                    (268435454u32, 34usize),
                    (268435454u32, 35usize),
                    (268435454u32, 36usize),
                    (268435454u32, 37usize),
                    (268435454u32, 38usize),
                    (268435454u32, 30usize),
                    (268435454u32, 40usize),
                    (268435454u32, 41usize),
                    (268435454u32, 42usize),
                    (268435454u32, 43usize),
                    (268435454u32, 44usize),
                    (268435454u32, 45usize),
                    (268435454u32, 46usize),
                    (268435454u32, 47usize),
                    (268435454u32, 39usize),
                ];
                let mut _vl = 0;
                while _vl < 5usize {
                    let (cached_idx, col_start, col_count) = VL_DESCS[_vl];
                    let mut expected: BabyBearExt4 = BabyBearExt4::ZERO;
                    let mut alpha_power: BabyBearExt4 = BabyBearExt4::ONE;
                    let mut _c = 0;
                    while _c < col_count {
                        let (col_constant, term_start, term_count) = VL_COLS[col_start + _c];
                        let mut col_val: BabyBearExt4 = BabyBearExt4::from_base(
                            BabyBearField::from_reduced_raw_repr(col_constant),
                        );
                        let mut _t = 0;
                        while _t < term_count {
                            let (coeff, dep_idx) = VL_TERMS[term_start + _t];
                            let mut t = *state.prev_claims.get_unchecked(dep_idx);
                            field_ops::mul_assign_by_base(
                                &mut t,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::add_assign(&mut col_val, &t);
                            _t += 1;
                        }
                        let mut term = col_val;
                        field_ops::mul_assign(&mut term, &alpha_power);
                        field_ops::add_assign(&mut expected, &term);
                        field_ops::mul_assign(&mut alpha_power, &lookup_alpha);
                        _c += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(E::gkr_vector_lookup_cache_relation_failed(1usize, _vl));
                    }
                    _vl += 1;
                }
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 1");
        }
        {
            let initial_claim = layer_0_compute_claim(
                state.prev_claims.as_array::<77usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 23usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                    nd_source,
                )?;
            let fc_len = 23usize;
            const NUM_AT_POINT_EVALS: usize = 111usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 0usize)?;
            }
            const NUM_EXTRA_EVALS: usize = 15usize;
            {
                let mut i = 0;
                while i < NUM_EXTRA_EVALS * EXT_DEGREE {
                    eval_buf.data_write(
                        data_words + i,
                        read_reduced_field_el::<I>(nd_source).as_u32_raw_repr(),
                    );
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, NUM_EXTRA_EVALS>::new();
            {
                let slice: &[BabyBearExt4] =
                    unsafe { eval_buf.data_as(NUM_AT_POINT_EVALS + NUM_EXTRA_EVALS) };
                let mut k = NUM_AT_POINT_EVALS;
                while k < NUM_AT_POINT_EVALS + NUM_EXTRA_EVALS {
                    extra_evals.push(unsafe { *slice.get_unchecked(k) });
                    k += 1;
                }
            }
            ts.commit(&mut eval_buf, data_words + NUM_EXTRA_EVALS * EXT_DEGREE);
            let next_batching = draw_single_field_el(ts);
            let final_step_evals: &[[BabyBearExt4; 1]] =
                unsafe { eval_buf.data_as(NUM_AT_POINT_EVALS) };
            state.prev_claims.clear();
            {
                const LAYOUT_KIND: [usize; 126usize] = [
                    1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 126usize] = [
                    0usize, 1usize, 58usize, 59usize, 2usize, 60usize, 61usize, 62usize, 63usize,
                    64usize, 65usize, 66usize, 3usize, 4usize, 67usize, 68usize, 69usize, 70usize,
                    71usize, 72usize, 73usize, 74usize, 75usize, 76usize, 77usize, 78usize,
                    79usize, 80usize, 81usize, 82usize, 83usize, 84usize, 85usize, 86usize,
                    87usize, 88usize, 89usize, 90usize, 0usize, 1usize, 2usize, 3usize, 4usize,
                    5usize, 6usize, 7usize, 8usize, 9usize, 10usize, 11usize, 12usize, 13usize,
                    14usize, 15usize, 16usize, 17usize, 18usize, 19usize, 20usize, 21usize,
                    22usize, 23usize, 24usize, 25usize, 26usize, 27usize, 28usize, 29usize,
                    30usize, 31usize, 32usize, 33usize, 34usize, 35usize, 36usize, 37usize,
                    38usize, 39usize, 40usize, 41usize, 42usize, 43usize, 44usize, 45usize,
                    46usize, 47usize, 48usize, 49usize, 50usize, 51usize, 52usize, 53usize,
                    54usize, 55usize, 56usize, 57usize, 5usize, 6usize, 7usize, 8usize, 9usize,
                    10usize, 11usize, 12usize, 13usize, 14usize, 91usize, 92usize, 93usize,
                    94usize, 95usize, 96usize, 97usize, 98usize, 99usize, 100usize, 101usize,
                    102usize, 103usize, 104usize, 105usize, 106usize, 107usize, 108usize, 109usize,
                    110usize,
                ];
                let mut i = 0usize;
                while i < 126usize {
                    let kind = unsafe { *LAYOUT_KIND.get_unchecked(i) };
                    let pos = unsafe { *LAYOUT_POS.get_unchecked(i) };
                    let claim: BabyBearExt4 = if kind == 0usize {
                        unsafe { final_step_evals.get_unchecked(pos)[0] }
                    } else {
                        *extra_evals.get(pos)
                    };
                    state.prev_claims.push(claim);
                    i += 1;
                }
            }
            {
                const SC_DESCS: [(usize, u32, usize, usize); 6usize] = [
                    (118usize, 0u32, 0usize, 3usize),
                    (119usize, 133099247u32, 3usize, 3usize),
                    (120usize, 1744830467u32, 6usize, 3usize),
                    (121usize, 133099247u32, 9usize, 3usize),
                    (122usize, 1476395013u32, 12usize, 3usize),
                    (123usize, 133099247u32, 15usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 18usize] = [
                    (1744830467u32, 24usize),
                    (268435454u32, 0usize),
                    (133099247u32, 90usize),
                    (1744830467u32, 25usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 90usize),
                    (1744830467u32, 24usize),
                    (268435454u32, 5usize),
                    (133099247u32, 91usize),
                    (1744830467u32, 25usize),
                    (268435454u32, 6usize),
                    (1744830467u32, 91usize),
                    (1744830467u32, 24usize),
                    (268435454u32, 12usize),
                    (133099247u32, 92usize),
                    (1744830467u32, 25usize),
                    (268435454u32, 13usize),
                    (1744830467u32, 92usize),
                ];
                let mut _sc = 0;
                while _sc < 6usize {
                    let (cached_idx, constant, term_start, term_count) = SC_DESCS[_sc];
                    let mut expected: BabyBearExt4 =
                        BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(constant));
                    let mut _t = 0;
                    while _t < term_count {
                        let (coeff, dep_idx) = SC_TERMS[term_start + _t];
                        let mut t = *state.prev_claims.get_unchecked(dep_idx);
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(coeff),
                        );
                        field_ops::add_assign(&mut expected, &t);
                        _t += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(E::gkr_single_lookup_cache_relation_failed(0usize, _sc));
                    }
                    _sc += 1;
                }
            }
            {
                const VL_DESCS: [(usize, usize, usize); 1usize] = [(124usize, 0usize, 10usize)];
                const VL_COLS: [(u32, usize, usize); 10usize] = [
                    (0u32, 0usize, 1usize),
                    (0u32, 1usize, 1usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (0u32, 8usize, 19usize),
                    (268435358u32, 27usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 27usize] = [
                    (268435454u32, 22usize),
                    (268435454u32, 23usize),
                    (268435454u32, 4usize),
                    (268435454u32, 38usize),
                    (268435454u32, 39usize),
                    (268435454u32, 40usize),
                    (268435454u32, 41usize),
                    (268435454u32, 42usize),
                    (268435454u32, 43usize),
                    (536870908u32, 44usize),
                    (1073741816u32, 45usize),
                    (134217711u32, 46usize),
                    (268435422u32, 47usize),
                    (536870844u32, 48usize),
                    (1073741688u32, 49usize),
                    (134217455u32, 50usize),
                    (268434910u32, 51usize),
                    (536869820u32, 52usize),
                    (1073739640u32, 53usize),
                    (134213359u32, 54usize),
                    (268426718u32, 55usize),
                    (536853436u32, 56usize),
                    (1073706872u32, 57usize),
                    (134147823u32, 58usize),
                    (268295646u32, 59usize),
                    (536591292u32, 9usize),
                    (1073182584u32, 16usize),
                ];
                let mut _vl = 0;
                while _vl < 1usize {
                    let (cached_idx, col_start, col_count) = VL_DESCS[_vl];
                    let mut expected: BabyBearExt4 = BabyBearExt4::ZERO;
                    let mut alpha_power: BabyBearExt4 = BabyBearExt4::ONE;
                    let mut _c = 0;
                    while _c < col_count {
                        let (col_constant, term_start, term_count) = VL_COLS[col_start + _c];
                        let mut col_val: BabyBearExt4 = BabyBearExt4::from_base(
                            BabyBearField::from_reduced_raw_repr(col_constant),
                        );
                        let mut _t = 0;
                        while _t < term_count {
                            let (coeff, dep_idx) = VL_TERMS[term_start + _t];
                            let mut t = *state.prev_claims.get_unchecked(dep_idx);
                            field_ops::mul_assign_by_base(
                                &mut t,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::add_assign(&mut col_val, &t);
                            _t += 1;
                        }
                        let mut term = col_val;
                        field_ops::mul_assign(&mut term, &alpha_power);
                        field_ops::add_assign(&mut expected, &term);
                        field_ops::mul_assign(&mut alpha_power, &lookup_alpha);
                        _c += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(E::gkr_vector_lookup_cache_relation_failed(0usize, _vl));
                    }
                    _vl += 1;
                }
            }
            {
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(125usize, 0usize, 10usize)];
                const VS_DEPS: [usize; 10usize] = [
                    96usize, 97usize, 98usize, 99usize, 100usize, 101usize, 102usize, 103usize,
                    104usize, 105usize,
                ];
                let mut _vs = 0;
                while _vs < 1usize {
                    let (cached_idx, dep_start, dep_count) = VS_DESCS[_vs];
                    let mut expected: BabyBearExt4 = BabyBearExt4::ZERO;
                    let mut alpha_power: BabyBearExt4 = BabyBearExt4::ONE;
                    let mut _d = 0;
                    while _d < dep_count {
                        let dep_idx = VS_DEPS[dep_start + _d];
                        let mut term = *state.prev_claims.get_unchecked(dep_idx);
                        field_ops::mul_assign(&mut term, &alpha_power);
                        field_ops::add_assign(&mut expected, &term);
                        field_ops::mul_assign(&mut alpha_power, &lookup_alpha);
                        _d += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(E::gkr_permutation_cache_relation_failed(0usize, _vs));
                    }
                    _vs += 1;
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                let addr_claim = *state.prev_claims.get_unchecked(4usize);
                field_ops::mul_assign(&mut t_addr, &addr_claim);
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(0usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(1usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(2usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(110usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 1usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let as_claim = *state.prev_claims.get_unchecked(9usize);
                field_ops::add_assign(&mut expected, &as_claim);
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let addr_claim = *state.prev_claims.get_unchecked(10usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let addr_claim = *state.prev_claims.get_unchecked(11usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(5usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(6usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(7usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(8usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(111usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 2usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                let addr_claim = *state.prev_claims.get_unchecked(4usize);
                field_ops::mul_assign(&mut t_addr, &addr_claim);
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(24usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(25usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(2usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(112usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 3usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let as_claim = *state.prev_claims.get_unchecked(9usize);
                field_ops::add_assign(&mut expected, &as_claim);
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let addr_claim = *state.prev_claims.get_unchecked(10usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let addr_claim = *state.prev_claims.get_unchecked(11usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(24usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(268435454u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(25usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(7usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(8usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(113usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 4usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let as_claim = *state.prev_claims.get_unchecked(16usize);
                field_ops::add_assign(&mut expected, &as_claim);
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let addr_claim = *state.prev_claims.get_unchecked(17usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let addr_claim = *state.prev_claims.get_unchecked(18usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(12usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(13usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(14usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(15usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(114usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 5usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(536870908u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(0u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(24usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(25usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(22usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(23usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(115usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 6usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let as_claim = *state.prev_claims.get_unchecked(16usize);
                field_ops::add_assign(&mut expected, &as_claim);
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let addr_claim = *state.prev_claims.get_unchecked(17usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_addr: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let addr_claim = *state.prev_claims.get_unchecked(18usize);
                    field_ops::mul_assign(&mut t_addr, &addr_claim);
                    field_ops::add_assign(&mut expected, &t_addr);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(24usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(25usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(19usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(20usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(116usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 7usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(536870908u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(0u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(28usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(29usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(26usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(27usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(117usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 8usize));
                }
            }
            check_virtual_setup_range_check_16bits::<E>(&state)?;
            check_virtual_setup_range_check_timestamp::<E>(&state)?;
            check_virtual_setup_inits_and_teardowns::<E>(&state)?;
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 0");
        }
        read_and_verify_pow::<I>(ts, BATCHED_PROXIMITY_POW_BITS, nd_source);
        state.batching_challenge = draw_single_field_el_after_pow(ts);
        let mut permutation_read_product: BabyBearExt4 = BabyBearExt4::ONE;
        let mut permutation_write_product: BabyBearExt4 = BabyBearExt4::ONE;
        #[allow(unused_mut)]
        let mut inits_and_teardowns_read_product: BabyBearExt4 = BabyBearExt4::ONE;
        #[allow(unused_mut)]
        let mut inits_and_teardowns_write_product: BabyBearExt4 = BabyBearExt4::ONE;
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
        {
            let mut acc_num = BabyBearExt4::ZERO;
            let mut acc_den = BabyBearExt4::ONE;
            for i in 0..16usize {
                let n = *evals_slice.get_unchecked(32usize + i);
                let d = *evals_slice.get_unchecked(48usize + i);
                field_ops::mul_assign(&mut acc_num, &d);
                let mut t = n;
                field_ops::mul_assign(&mut t, &acc_den);
                field_ops::add_assign(&mut acc_num, &t);
                field_ops::mul_assign(&mut acc_den, &d);
            }
            if !acc_num.is_zero() || acc_den.is_zero() {
                return Err(E::gkr_lookup_identity_failed(0usize));
            }
        }
        {
            let mut acc_num = BabyBearExt4::ZERO;
            let mut acc_den = BabyBearExt4::ONE;
            for i in 0..16usize {
                let n = *evals_slice.get_unchecked(64usize + i);
                let d = *evals_slice.get_unchecked(80usize + i);
                field_ops::mul_assign(&mut acc_num, &d);
                let mut t = n;
                field_ops::mul_assign(&mut t, &acc_den);
                field_ops::add_assign(&mut acc_num, &t);
                field_ops::mul_assign(&mut acc_den, &d);
            }
            if !acc_num.is_zero() || acc_den.is_zero() {
                return Err(E::gkr_lookup_identity_failed(1usize));
            }
        }
        {
            let mut acc_num = BabyBearExt4::ZERO;
            let mut acc_den = BabyBearExt4::ONE;
            for i in 0..16usize {
                let n = *evals_slice.get_unchecked(96usize + i);
                let d = *evals_slice.get_unchecked(112usize + i);
                field_ops::mul_assign(&mut acc_num, &d);
                let mut t = n;
                field_ops::mul_assign(&mut t, &acc_den);
                field_ops::add_assign(&mut acc_num, &t);
                field_ops::mul_assign(&mut acc_den, &d);
            }
            if !acc_num.is_zero() || acc_den.is_zero() {
                return Err(E::gkr_lookup_identity_failed(2usize));
            }
        }
        {
            let mut it_read = BabyBearExt4::ONE;
            for i in 0..16usize {
                let eval = *evals_slice.get_unchecked(128usize + i);
                field_ops::mul_assign(&mut it_read, &eval);
            }
            let mut it_write = BabyBearExt4::ONE;
            for i in 0..16usize {
                let eval = *evals_slice.get_unchecked(144usize + i);
                field_ops::mul_assign(&mut it_write, &eval);
            }
            inits_and_teardowns_read_product = it_read;
            inits_and_teardowns_write_product = it_write;
        }
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log("GKR MAIN OUTPUT");
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            permutation_read_product,
            permutation_write_product,
            inits_and_teardowns_read_product,
            inits_and_teardowns_write_product,
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
        CLAIM_POINT_CAPACITY,
        GKR_ADDRS,
    > for VerifierImplementation
{
    #[inline(always)]
    fn verify_gkr<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
        external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
        nd_source: &mut I,
    ) -> Result<ConcreteGKRVerifierOutput, E::Error> {
        verify_gkr::<I, E>(
            external_challenges,
            initial_transcript,
            transcript_state,
            nd_source,
        )
    }
    #[inline(always)]
    fn verify_whir<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
        whir_batching_challenge: BabyBearExt4,
        base_layer_claims: &[BabyBearExt4],
        initial_claim_point: &[BabyBearExt4],
        nd_source: &mut I,
    ) -> Result<(), E::Error> {
        super::whir::verify_whir::<I, E>(
            initial_transcript,
            transcript_state,
            whir_batching_challenge,
            base_layer_claims,
            initial_claim_point,
            nd_source,
        )
    }
}
