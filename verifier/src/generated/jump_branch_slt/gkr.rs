use super::common::{
    commit_field_els, dot_eq, draw_field_els_into, fold_standard_claims, make_eq_poly,
    read_field_el, read_field_els, verify_final_step_check, verify_sumcheck_rounds,
};
use super::constants::*;
use verifier_common::blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use verifier_common::cs::definitions::GKRAddress;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{
    commit_eval_buffer, read_eval_data_from_nds, GKRVerificationError, GKRVerifierOutput,
    LayerState, LazyVec,
};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::transcript::{Blake2sTranscript, Seed};
#[inline(always)]
unsafe fn layer_0_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(2usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(3usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(4usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(5usize);
        let c1 = output_claims.get(6usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(7usize);
        let c1 = output_claims.get(8usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(9usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(10usize);
        let c1 = output_claims.get(11usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(12usize);
        let c1 = output_claims.get(13usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(14usize);
        let c1 = output_claims.get(15usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(16usize);
        let c1 = output_claims.get(17usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(18usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(19usize);
        let c1 = output_claims.get(20usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(21usize);
        let c1 = output_claims.get(22usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(23usize);
        let c1 = output_claims.get(24usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    combined
}
#[inline(always)]
unsafe fn layer_0_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(31usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(41usize) }[j];
            let vb = unsafe { evals.get_unchecked(42usize) }[j];
            field_ops::mul_assign(&mut val, &vb);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(43usize) }[j];
            let vb = unsafe { evals.get_unchecked(44usize) }[j];
            field_ops::mul_assign(&mut val, &vb);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(45usize) }[j];
            let vb = unsafe { evals.get_unchecked(46usize) }[j];
            field_ops::mul_assign(&mut val, &vb);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(47usize) }[j];
            let vb = unsafe { evals.get_unchecked(48usize) }[j];
            field_ops::mul_assign(&mut val, &vb);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(7usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(39usize) }[j];
            let mut cb_g = unsafe { evals.get_unchecked(22usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                field_ops::mul_assign(&mut cb_g, &b_g);
                let mut num = d_g;
                field_ops::sub_assign(&mut num, &cb_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(8usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(33usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = b_g;
                field_ops::add_assign(&mut num, &d_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(9usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(37usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(40usize) }[j];
            let mut cb_g = unsafe { evals.get_unchecked(23usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                field_ops::mul_assign(&mut cb_g, &b_g);
                let mut num = d_g;
                field_ops::sub_assign(&mut num, &cb_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(38usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(49usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = b_g;
                field_ops::add_assign(&mut num, &d_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(50usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(51usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = b_g;
                field_ops::add_assign(&mut num, &d_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(52usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(53usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = b_g;
                field_ops::add_assign(&mut num, &d_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(54usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(31usize) }[j];
            let mut b = unsafe { evals.get_unchecked(55usize) }[j];
            let c = unsafe { evals.get_unchecked(24usize) }[j];
            let mut d = unsafe { evals.get_unchecked(56usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b, &lookup_additive_challenge);
                field_ops::add_assign(&mut d, &lookup_additive_challenge);
                let mut ad = a;
                field_ops::mul_assign(&mut ad, &d);
                let mut cb = c;
                field_ops::mul_assign(&mut cb, &b);
                field_ops::sub_assign(&mut ad, &cb);
                ad
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(57usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(58usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = b_g;
                field_ops::add_assign(&mut num, &d_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut b_g = unsafe { evals.get_unchecked(59usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(60usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut b_g, &lookup_additive_challenge);
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = b_g;
                field_ops::add_assign(&mut num, &d_g);
                num
            };
            let out1 = {
                let mut den = b_g;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = {
                let mut result = BabyBearExt4::ZERO;
                {
                    let mut t = unsafe { *challenge_powers.get_unchecked(11usize) };
                    field_ops::mul_assign_by_base(
                        &mut t,
                        &BabyBearField::from_reduced_raw_repr(1509916673u32),
                    );
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let mut t = unsafe { *challenge_powers.get_unchecked(12usize) };
                    field_ops::mul_assign_by_base(
                        &mut t,
                        &BabyBearField::from_reduced_raw_repr(2013233153u32),
                    );
                    field_ops::add_assign(&mut result, &t);
                }
                {
                    let val = unsafe { evals.get_unchecked(2usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1073741816u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(13usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(3usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1073741816u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(14usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(4usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1073741816u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(15usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(5usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1073741816u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(16usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(6usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(17usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(10usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(18usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(11usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(19usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(12usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(20usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(13usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(21usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(15usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(3usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(939524105u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(17usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(7usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(9usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(18usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(8usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(10usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(19usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(22usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(20usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(23usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(21usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(24usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(29usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(9usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(30usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(10usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(31usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(0usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(34usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(11usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1761599489u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(12usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(2013257729u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(35usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(12usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(37usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(11usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(251666432u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(12usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(8192u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let val = unsafe { evals.get_unchecked(38usize) }[j];
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(12usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(0usize) }[j];
                    let vb = unsafe { evals.get_unchecked(2usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(0usize) }[j];
                    let vb = unsafe { evals.get_unchecked(3usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(0usize) }[j];
                    let vb = unsafe { evals.get_unchecked(4usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(0usize) }[j];
                    let vb = unsafe { evals.get_unchecked(15usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(1usize) }[j];
                    let vb = unsafe { evals.get_unchecked(2usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(1usize) }[j];
                    let vb = unsafe { evals.get_unchecked(3usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(1usize) }[j];
                    let vb = unsafe { evals.get_unchecked(4usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(1usize) }[j];
                    let vb = unsafe { evals.get_unchecked(15usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(2usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(13usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(7usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(7usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(8usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(8usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(9usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(10usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(11usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(12usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(13usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(16usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(6usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(2usize) }[j];
                    let vb = unsafe { evals.get_unchecked(36usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(3usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(14usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(7usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(7usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(8usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(8usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(9usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(10usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(11usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(12usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(13usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(16usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(6usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(25usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(26usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(3usize) }[j];
                    let vb = unsafe { evals.get_unchecked(36usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(4usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(15usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(7usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(8usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(9usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(10usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(11usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(12usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(13usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(14usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(7usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(25usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(26usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(27usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(28usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(4usize) }[j];
                    let vb = unsafe { evals.get_unchecked(36usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(5usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(16usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(7usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(8usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(9usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(10usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(11usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(12usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(13usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744970275u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(14usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(3usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(25usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(26usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(27usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(28usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(5usize) }[j];
                    let vb = unsafe { evals.get_unchecked(36usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(6usize) }[j];
                    let vb = unsafe { evals.get_unchecked(6usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(17usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(6usize) }[j];
                    let vb = unsafe { evals.get_unchecked(17usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(9usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(6usize) }[j];
                    let vb = unsafe { evals.get_unchecked(18usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(10usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1744830467u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(10usize) }[j];
                    let vb = unsafe { evals.get_unchecked(10usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(18usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(11usize) }[j];
                    let vb = unsafe { evals.get_unchecked(11usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(19usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(12usize) }[j];
                    let vb = unsafe { evals.get_unchecked(12usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(20usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(13usize) }[j];
                    let vb = unsafe { evals.get_unchecked(13usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(21usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(15usize) }[j];
                    let vb = unsafe { evals.get_unchecked(16usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(6usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(19usize) }[j];
                    let vb = unsafe { evals.get_unchecked(19usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(22usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(20usize) }[j];
                    let vb = unsafe { evals.get_unchecked(20usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(23usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(21usize) }[j];
                    let vb = unsafe { evals.get_unchecked(21usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(24usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(31usize) }[j];
                    let vb = unsafe { evals.get_unchecked(31usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(0usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(32usize) }[j];
                    let vb = unsafe { evals.get_unchecked(2usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(32usize) }[j];
                    let vb = unsafe { evals.get_unchecked(3usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(1usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(32usize) }[j];
                    let vb = unsafe { evals.get_unchecked(4usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(32usize) }[j];
                    let vb = unsafe { evals.get_unchecked(5usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(4usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(33usize) }[j];
                    let vb = unsafe { evals.get_unchecked(2usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(33usize) }[j];
                    let vb = unsafe { evals.get_unchecked(3usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(2usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(33usize) }[j];
                    let vb = unsafe { evals.get_unchecked(4usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(33usize) }[j];
                    let vb = unsafe { evals.get_unchecked(5usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(5usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(268435454u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(34usize) }[j];
                    let vb = unsafe { evals.get_unchecked(34usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(11usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1981808641u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(34usize) }[j];
                    let vb = unsafe { evals.get_unchecked(37usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(11usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(62914560u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                {
                    let va = unsafe { evals.get_unchecked(37usize) }[j];
                    let vb = unsafe { evals.get_unchecked(37usize) }[j];
                    let mut prod = va;
                    field_ops::mul_assign(&mut prod, &vb);
                    {
                        let mut t = unsafe { *challenge_powers.get_unchecked(11usize) };
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(1981808641u32),
                        );
                        field_ops::mul_assign(&mut t, &prod);
                        field_ops::add_assign(&mut result, &t);
                    }
                }
                result
            };
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
unsafe fn layer_1_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(2usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(3usize);
        let c1 = output_claims.get(4usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(5usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(6usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(7usize);
        let c1 = output_claims.get(8usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(9usize);
        let c1 = output_claims.get(10usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(11usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(12usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(13usize);
        let c1 = output_claims.get(14usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(15usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        let claim = output_claims.get(16usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    combined
}
#[inline(always)]
unsafe fn layer_1_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(0usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(1usize) }[j];
            let vb = unsafe { evals.get_unchecked(3usize) }[j];
            field_ops::mul_assign(&mut val, &vb);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(2usize) }[j];
            let vb = unsafe { evals.get_unchecked(4usize) }[j];
            field_ops::mul_assign(&mut val, &vb);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(7usize) }[j];
            let b = unsafe { evals.get_unchecked(8usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(9usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = a;
                field_ops::mul_assign(&mut num, &d_g);
                field_ops::add_assign(&mut num, &b);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(5usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(6usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(16usize) }[j];
            let b = unsafe { evals.get_unchecked(17usize) }[j];
            let mut d_g = unsafe { evals.get_unchecked(18usize) }[j];
            let out0 = {
                field_ops::add_assign(&mut d_g, &lookup_additive_challenge);
                let mut num = a;
                field_ops::mul_assign(&mut num, &d_g);
                field_ops::add_assign(&mut num, &b);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d_g);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(14usize) }[j];
            let b = unsafe { evals.get_unchecked(15usize) }[j];
            let c = unsafe { evals.get_unchecked(12usize) }[j];
            let d = unsafe { evals.get_unchecked(13usize) }[j];
            let out0 = {
                let mut num = a;
                field_ops::mul_assign(&mut num, &d);
                let mut cb_tmp = c;
                field_ops::mul_assign(&mut cb_tmp, &b);
                field_ops::add_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(10usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(11usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(23usize) }[j];
            let b = unsafe { evals.get_unchecked(24usize) }[j];
            let c = unsafe { evals.get_unchecked(21usize) }[j];
            let d = unsafe { evals.get_unchecked(22usize) }[j];
            let out0 = {
                let mut num = a;
                field_ops::mul_assign(&mut num, &d);
                let mut cb_tmp = c;
                field_ops::mul_assign(&mut cb_tmp, &b);
                field_ops::add_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(19usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(20usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
unsafe fn layer_2_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(2usize);
        let c1 = output_claims.get(3usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(4usize);
        let c1 = output_claims.get(5usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(6usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(7usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        let c0 = output_claims.get(8usize);
        let c1 = output_claims.get(9usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        field_ops::add_assign(&mut combined, &t0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut combined, &t1);
    }
    combined
}
#[inline(always)]
unsafe fn layer_2_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(1usize) }[j];
            let mask_val = unsafe { evals.get_unchecked(0usize) }[j];
            field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
            field_ops::mul_assign(&mut val, &mask_val);
            field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = unsafe { evals.get_unchecked(2usize) }[j];
            let mask_val = unsafe { evals.get_unchecked(0usize) }[j];
            field_ops::sub_assign_base(&mut val, &BabyBearField::ONE);
            field_ops::mul_assign(&mut val, &mask_val);
            field_ops::add_assign_base(&mut val, &BabyBearField::ONE);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(5usize) }[j];
            let b = unsafe { evals.get_unchecked(6usize) }[j];
            let c = unsafe { evals.get_unchecked(3usize) }[j];
            let d = unsafe { evals.get_unchecked(4usize) }[j];
            let out0 = {
                let mut num = a;
                field_ops::mul_assign(&mut num, &d);
                let mut cb_tmp = c;
                field_ops::mul_assign(&mut cb_tmp, &b);
                field_ops::add_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(11usize) }[j];
            let b = unsafe { evals.get_unchecked(12usize) }[j];
            let c = unsafe { evals.get_unchecked(9usize) }[j];
            let d = unsafe { evals.get_unchecked(10usize) }[j];
            let out0 = {
                let mut num = a;
                field_ops::mul_assign(&mut num, &d);
                let mut cb_tmp = c;
                field_ops::mul_assign(&mut cb_tmp, &b);
                field_ops::add_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(7usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(8usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(15usize) }[j];
            let b = unsafe { evals.get_unchecked(16usize) }[j];
            let c = unsafe { evals.get_unchecked(13usize) }[j];
            let d = unsafe { evals.get_unchecked(14usize) }[j];
            let out0 = {
                let mut num = a;
                field_ops::mul_assign(&mut num, &d);
                let mut cb_tmp = c;
                field_ops::mul_assign(&mut cb_tmp, &b);
                field_ops::add_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    acc
}
#[inline(always)]
unsafe fn layer_3_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let c0 = output_claims.get(0usize);
        let c1 = output_claims.get(1usize);
        let mut t0 = bc0;
        field_ops::mul_assign(&mut t0, &c0);
        let mut t1 = bc1;
        field_ops::mul_assign(&mut t1, &c1);
        field_ops::add_assign(&mut t0, &t1);
        t0
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(2usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(3usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(4usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(5usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(6usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc = current_batch;
        let claim = output_claims.get(7usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    combined
}
#[inline(always)]
unsafe fn layer_3_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    challenge_powers: &[BabyBearExt4; GKR_MAX_POW],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let a = unsafe { evals.get_unchecked(6usize) }[j];
            let b = unsafe { evals.get_unchecked(7usize) }[j];
            let c = unsafe { evals.get_unchecked(4usize) }[j];
            let d = unsafe { evals.get_unchecked(5usize) }[j];
            let out0 = {
                let mut num = a;
                field_ops::mul_assign(&mut num, &d);
                let mut cb_tmp = c;
                field_ops::mul_assign(&mut cb_tmp, &b);
                field_ops::add_assign(&mut num, &cb_tmp);
                num
            };
            let out1 = {
                let mut den = b;
                field_ops::mul_assign(&mut den, &d);
                den
            };
            let mut c0 = bc0;
            field_ops::mul_assign(&mut c0, &out0);
            let mut c1 = bc1;
            field_ops::mul_assign(&mut c1, &out1);
            field_ops::add_assign(&mut acc[j], &c0);
            field_ops::add_assign(&mut acc[j], &c1);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(0usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(1usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(2usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(3usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(8usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = unsafe { evals.get_unchecked(9usize) }[j];
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_4_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_4_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(2usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(0usize) };
        let v1 = unsafe { evals.get_unchecked(1usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_5_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_5_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_6_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_6_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_7_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_7_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_8_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_8_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_9_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_9_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_10_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_10_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_11_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_11_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_12_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_12_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_13_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_13_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_14_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_14_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_15_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_15_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_16_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_16_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_17_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_17_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_18_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_18_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_19_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_19_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_20_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_20_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_21_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_21_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_22_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_22_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[inline(always)]
unsafe fn dim_reducing_23_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = output_claims.get(1usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        field_ops::add_assign(&mut combined, &t);
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 2usize), (bc1, 3usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 4usize), (bc1, 5usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for (bc, idx) in [(bc0, 6usize), (bc1, 7usize)] {
            let claim = output_claims.get(idx);
            let mut t = bc;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
        }
    }
    combined
}
#[inline(always)]
unsafe fn dim_reducing_23_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
        {
            let v0a = unsafe { *v0.get_unchecked(0usize) };
            let v0b = unsafe { *v0.get_unchecked(1usize) };
            let v1a = unsafe { *v1.get_unchecked(0usize) };
            let v1b = unsafe { *v1.get_unchecked(1usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[0usize], &c0_tmp);
            field_ops::add_assign(&mut acc[0usize], &c1_tmp);
        }
        {
            let v0a = unsafe { *v0.get_unchecked(2usize) };
            let v0b = unsafe { *v0.get_unchecked(3usize) };
            let v1a = unsafe { *v1.get_unchecked(2usize) };
            let v1b = unsafe { *v1.get_unchecked(3usize) };
            let mut num = v0a;
            field_ops::mul_assign(&mut num, &v1b);
            let mut cb_tmp = v0b;
            field_ops::mul_assign(&mut cb_tmp, &v1a);
            field_ops::add_assign(&mut num, &cb_tmp);
            let mut den = v1a;
            field_ops::mul_assign(&mut den, &v1b);
            let mut c0_tmp = bc0;
            field_ops::mul_assign(&mut c0_tmp, &num);
            let mut c1_tmp = bc1;
            field_ops::mul_assign(&mut c1_tmp, &den);
            field_ops::add_assign(&mut acc[1usize], &c0_tmp);
            field_ops::add_assign(&mut acc[1usize], &c1_tmp);
        }
    }
    acc
}
#[allow(unused_braces, unused_mut, unused_variables, unused_unsafe)]
pub fn verify_gkr_sumcheck<I: NonDeterminismSource>(
) -> Result<GKRVerifierOutput<'static, BabyBearExt4, GKR_ROUNDS, GKR_ADDRS>, GKRVerificationError> {
    unsafe {
        let mut transcript_buf = LazyVec::<u32, GKR_TRANSCRIPT_U32>::new();
        for _ in 0..GKR_TRANSCRIPT_U32 {
            transcript_buf.push(I::read_word());
        }
        let mut seed = Blake2sTranscript::commit_initial(transcript_buf.as_slice());
        let mut hasher = DelegatedBlake2sState::new();
        let mut init_challenges = [BabyBearExt4::ZERO; 3];
        draw_field_els_into(&mut hasher, &mut seed, &mut init_challenges);
        let lookup_additive_challenge = init_challenges[1];
        let constraints_batch_challenge = init_challenges[2];
        let mut evals_flat = [core::mem::MaybeUninit::<BabyBearExt4>::uninit(); GKR_EVALS];
        let evals_slice = unsafe {
            let dst = core::slice::from_raw_parts_mut(
                evals_flat.as_mut_ptr().cast::<BabyBearExt4>(),
                128usize,
            );
            read_field_els::<I>(dst);
            core::slice::from_raw_parts(evals_flat.as_ptr().cast::<BabyBearExt4>(), 128usize)
        };
        commit_field_els(&mut seed, evals_slice);
        let mut all_challenges = [BabyBearExt4::ZERO; GKR_ROUNDS + 1];
        draw_field_els_into(&mut hasher, &mut seed, &mut all_challenges[..5usize]);
        let batching_challenge = all_challenges[5usize - 1];
        let mut eq_buf = LazyVec::<BabyBearExt4, 16usize>::new();
        let eq_challenges: &[BabyBearExt4; 4usize] =
            all_challenges[..4usize].try_into().unwrap_unchecked();
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
        let mut prev_point = [BabyBearExt4::ZERO; GKR_ROUNDS];
        prev_point[..4usize].copy_from_slice(&all_challenges[..4usize]);
        let mut state = LayerState {
            prev_point,
            prev_point_len: 4usize,
            prev_claims,
            batching_challenge,
        };
        let mut eval_buf = AlignedArray64::<u32, GKR_EVAL_BUF>::new_uninit();
        {
            let initial_claim =
                dim_reducing_23_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 3usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    23usize,
                )?;
            let mut fc_len = 3usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_23_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    23usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_22_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 4usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                )?;
            let mut fc_len = 4usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_22_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    22usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_21_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 5usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                )?;
            let mut fc_len = 5usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_21_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    21usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_20_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 6usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                )?;
            let mut fc_len = 6usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_20_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    20usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_19_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 7usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                )?;
            let mut fc_len = 7usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_19_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    19usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_18_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 8usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                )?;
            let mut fc_len = 8usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_18_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    18usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_17_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 9usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                )?;
            let mut fc_len = 9usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_17_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    17usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_16_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 10usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                )?;
            let mut fc_len = 10usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_16_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    16usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_15_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 11usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                )?;
            let mut fc_len = 11usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_15_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    15usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_14_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 12usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                )?;
            let mut fc_len = 12usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_14_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    14usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_13_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 13usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                )?;
            let mut fc_len = 13usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_13_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    13usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_12_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 14usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                )?;
            let mut fc_len = 14usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_12_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    12usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_11_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 15usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                )?;
            let mut fc_len = 15usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_11_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    11usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_10_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 16usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                )?;
            let mut fc_len = 16usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_10_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    10usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_9_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 17usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                )?;
            let mut fc_len = 17usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_9_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    9usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_8_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 18usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                )?;
            let mut fc_len = 18usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_8_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    8usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_7_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_7_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    7usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_6_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 20usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 20usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_6_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    6usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_5_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_5_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    5usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim =
                dim_reducing_4_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 22usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 22usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = dim_reducing_4_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    4usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 3];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let r_before_last = draw_buf[0];
            let r_last = draw_buf[1];
            let next_batching = draw_buf[2];
            *state.prev_point.get_unchecked_mut(fc_len) = r_before_last;
            fc_len += 1;
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 2;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq4 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_before_last, r_last], &mut eq4);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
            let eq4_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq4.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq4_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        let challenge_powers: [BabyBearExt4; GKR_MAX_POW] = {
            let mut lv = LazyVec::<BabyBearExt4, GKR_MAX_POW>::new();
            let mut pow = BabyBearExt4::ONE;
            for _ in 0..GKR_MAX_POW {
                lv.push(pow);
                field_ops::mul_assign(&mut pow, &constraints_batch_challenge);
            }
            unsafe { lv.into_array() }
        };
        {
            let initial_claim = layer_3_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 23usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 10usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 10usize);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    3usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 2];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let last_r = draw_buf[0];
            let next_batching = draw_buf[1];
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<10usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_2_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 23usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 17usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 17usize);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    2usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 2];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let last_r = draw_buf[0];
            let next_batching = draw_buf[1];
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<17usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_1_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 23usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 25usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 25usize);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    1usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 2];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let last_r = draw_buf[0];
            let next_batching = draw_buf[1];
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            fold_standard_claims::<25usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                last_r,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        {
            let initial_claim = layer_0_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 23usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 23usize;
            let data_words = 61usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 61usize);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    0usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = [BabyBearExt4::ZERO; 2];
            draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
            let last_r = draw_buf[0];
            let next_batching = draw_buf[1];
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            let mut extra_evals = [BabyBearExt4::ZERO; 25usize];
            read_field_els::<I>(&mut extra_evals);
            commit_field_els(&mut seed, &extra_evals);
            let final_step_evals: &[[BabyBearExt4; 2]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 61usize);
            state.prev_claims.clear();
            {
                let ev = unsafe { final_step_evals.get_unchecked(0usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(1usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[0usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(2usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(3usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(4usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(5usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(6usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(7usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(8usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(9usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(10usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(11usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(12usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(13usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[1usize]);
            state.prev_claims.push(extra_evals[2usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(14usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(15usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(16usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(17usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(18usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(19usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(20usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(21usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(22usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(23usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(24usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[3usize]);
            state.prev_claims.push(extra_evals[4usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(25usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(26usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[5usize]);
            state.prev_claims.push(extra_evals[6usize]);
            state.prev_claims.push(extra_evals[7usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(27usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(28usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[8usize]);
            state.prev_claims.push(extra_evals[9usize]);
            state.prev_claims.push(extra_evals[10usize]);
            state.prev_claims.push(extra_evals[11usize]);
            state.prev_claims.push(extra_evals[12usize]);
            state.prev_claims.push(extra_evals[13usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(29usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(30usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(31usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(32usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(33usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(34usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(35usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[14usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(36usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(37usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(38usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(39usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(40usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.prev_claims.push(extra_evals[15usize]);
            state.prev_claims.push(extra_evals[16usize]);
            state.prev_claims.push(extra_evals[17usize]);
            state.prev_claims.push(extra_evals[18usize]);
            state.prev_claims.push(extra_evals[19usize]);
            state.prev_claims.push(extra_evals[20usize]);
            state.prev_claims.push(extra_evals[21usize]);
            state.prev_claims.push(extra_evals[22usize]);
            state.prev_claims.push(extra_evals[23usize]);
            state.prev_claims.push(extra_evals[24usize]);
            {
                let ev = unsafe { final_step_evals.get_unchecked(41usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(42usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(43usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(44usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(45usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(46usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(47usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(48usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(49usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(50usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(51usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(52usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(53usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(54usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(55usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(56usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(57usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(58usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(59usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            {
                let ev = unsafe { final_step_evals.get_unchecked(60usize) };
                let f0 = ev[0];
                let mut diff = ev[1];
                field_ops::sub_assign(&mut diff, &f0);
                field_ops::mul_assign(&mut diff, &last_r);
                field_ops::add_assign(&mut diff, &f0);
                state.prev_claims.push(diff);
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        let grand_product_accumulator: BabyBearExt4 = read_field_el::<I>();
        commit_field_els(&mut seed, &[grand_product_accumulator]);
        let mut draw_buf = [BabyBearExt4::ZERO; 1];
        draw_field_els_into(&mut hasher, &mut seed, &mut draw_buf);
        let whir_batching_challenge = draw_buf[0];
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            base_layer_addrs: LAYER_0_SORTED_ADDRS,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            grand_product_accumulator,
            additional_base_layer_openings: BASE_LAYER_ADDITIONAL_OPENINGS,
            whir_batching_challenge,
            whir_transcript_seed: seed,
        })
    }
}
