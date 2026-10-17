use verifier::add_sub_lui_auipc_mop::sec_100::common::compute_claim;
use verifier::field::baby_bear::base::BabyBearField;
use verifier::field::baby_bear::ext4::BabyBearExt4;
use verifier::field::{Field, FieldExtension};

fn ext(seed: u32) -> BabyBearExt4 {
    <BabyBearExt4 as FieldExtension<BabyBearField>>::from_coeffs(core::array::from_fn(|i| {
        BabyBearField::from_nonreduced_u32(seed.wrapping_mul(0x9e37_79b9) ^ (i as u32 * 7919))
    }))
}

#[test]
fn compute_claim_matches_naive_batching() {
    let claims: Vec<BabyBearExt4> = (0..6).map(|i| ext(10 + i)).collect();
    let batch_base = ext(1);
    // `(n, o0, o1)`: `n == 0` skips a power, otherwise the first `n` of `o0`, `o1` take the next ones.
    let descs = [
        (0, 0, 0),
        (1, 3, 0),
        (0, 0, 0),
        (2, 0, 5),
        (1, 1, 0),
        (0, 0, 0),
        (2, 4, 2),
        (0, 0, 0),
    ];

    let mut expected = BabyBearExt4::ZERO;
    let mut power = BabyBearExt4::ONE;
    for &(n, o0, o1) in descs.iter() {
        if n == 0 {
            power.mul_assign(&batch_base);
        }
        for o in [o0, o1].into_iter().take(n) {
            let mut term = claims[o];
            term.mul_assign(&power);
            expected.add_assign(&term);
            power.mul_assign(&batch_base);
        }
    }

    let combined = unsafe { compute_claim(&claims, &descs, batch_base) };
    assert_eq!(combined, expected);
}
