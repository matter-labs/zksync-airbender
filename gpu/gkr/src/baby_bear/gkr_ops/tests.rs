use era_cudart::{
    memory::{memory_copy_async, DeviceAllocation},
    stream::CudaStream,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_hash::blake2s::STATE_SIZE;
use rand::Rng;

use crate::{
    gkr_ops::tests::claims_parity_suite,
    upstream::{Field, Seed},
};

fn sample_e4(seed: u32) -> E4 {
    use field::PrimeField;
    E4::from_array_of_base([
        BF::from_u32_with_reduction(seed.wrapping_mul(0x9E3779B1)),
        BF::from_u32_with_reduction(seed.wrapping_mul(0x85EBCA77)),
        BF::from_u32_with_reduction(seed.wrapping_mul(0xC2B2AE3D)),
        BF::from_u32_with_reduction(seed.wrapping_mul(0x27D4EB2F)),
    ])
}

/// Reference host-side implementation of the sumcheck Lagrange interpolant
/// at (0, 1, random_point). Mirrors `whir_fold::special_lagrange_interpolate`,
/// inlined here so this module's tests stay self-contained.
fn special_lagrange_interpolate_host(
    eval_at_0: E4,
    eval_at_1: E4,
    eval_at_random: E4,
    random_point: E4,
) -> [E4; 3] {
    use field::Field;

    let mut coeffs_for_0 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_0[1] = E4::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();
    coeffs_for_0[0] = random_point;

    let mut coeffs_for_1 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_1[1] = random_point;
    coeffs_for_1[1].negate();

    let mut coeffs_for_random = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_random[1] = E4::ONE;
    coeffs_for_random[1].negate();

    let mut dens = [E4::ONE, E4::ONE, E4::ONE];
    let mut t = E4::ZERO;
    t.sub_assign(&E4::ONE);
    dens[0].mul_assign(&t);
    let mut t = E4::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E4::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let t = random_point;
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E4::ONE);
    dens[2].mul_assign(&t);

    for d in dens.iter_mut() {
        *d = d.inverse().expect("non-zero denominator");
    }

    let mut result = [E4::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random),
    ] {
        for (dst, coeff) in result.iter_mut().zip(coeffs) {
            let mut term = coeff;
            term.mul_assign(&den);
            term.mul_assign(&eval);
            dst.add_assign(&term);
        }
    }
    result
}

/// Runs the exact host-side per-round callback logic and returns the
/// updated state plus the derived sumcheck coefficients and challenge.
fn host_whir_fold_round_update(
    mut seed: Seed,
    f_at_0: E4,
    f_at_1: E4,
    raw_half_input: E4,
) -> (Seed, [E4; 3], E4) {
    use field::{Field, FieldExtension, PrimeField};
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};

    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let mut f_half = raw_half_input;
    f_half.mul_assign_by_base(&quart);

    let coeffs = special_lagrange_interpolate_host(f_at_0, f_at_1, f_half, E4::from_base(two_inv));
    commit_field_els::<BF, E4, prover::transcript::Blake2sTranscript>(&mut seed, &coeffs);
    let challenge =
        draw_random_field_els::<BF, E4, prover::transcript::Blake2sTranscript>(&mut seed, 1)[0];
    (seed, coeffs, challenge)
}

fn run_device_whir_fold_round_update(
    seed_in: Seed,
    f_at_0: E4,
    f_at_1: E4,
    raw_half_input: E4,
) -> (Seed, [E4; 3], E4) {
    let stream = CudaStream::default();

    let mut d_reduction: DeviceAllocation<E4> = DeviceAllocation::alloc(3).unwrap();
    memory_copy_async(&mut d_reduction, &[f_at_0, f_at_1, raw_half_input], &stream).unwrap();

    let mut d_seed: DeviceAllocation<u32> = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    memory_copy_async(&mut d_seed, &seed_in.0[..], &stream).unwrap();

    let mut d_coeffs: DeviceAllocation<E4> = DeviceAllocation::alloc(3).unwrap();
    let mut d_challenge: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();

    crate::baby_bear::gkr_ops::whir_fold_round_update(
        &d_reduction,
        &mut d_seed,
        &mut d_coeffs,
        &mut d_challenge,
        &stream,
    )
    .unwrap();

    let mut seed_out = Seed::default();
    let mut coeffs_out = [E4::ZERO; 3];
    let mut challenge_out = [E4::ZERO];
    memory_copy_async(&mut seed_out.0[..], &d_seed, &stream).unwrap();
    memory_copy_async(&mut coeffs_out[..], &d_coeffs, &stream).unwrap();
    memory_copy_async(&mut challenge_out[..], &d_challenge, &stream).unwrap();
    stream.synchronize().unwrap();

    (seed_out, coeffs_out, challenge_out[0])
}

fn assert_whir_fold_round_parity(seed_in: Seed, f_at_0: E4, f_at_1: E4, raw_half_input: E4) {
    let (h_seed, h_coeffs, h_challenge) =
        host_whir_fold_round_update(seed_in, f_at_0, f_at_1, raw_half_input);
    let (d_seed, d_coeffs, d_challenge) =
        run_device_whir_fold_round_update(seed_in, f_at_0, f_at_1, raw_half_input);
    assert_eq!(d_seed.0, h_seed.0, "seed mismatch");
    assert_eq!(d_coeffs, h_coeffs, "coeffs mismatch");
    assert_eq!(d_challenge, h_challenge, "challenge mismatch");
}

#[test]
fn whir_fold_round_update_parity_fixed() {
    let seed = Seed([
        0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555, 0x66666666, 0x77777777,
        0x88888888,
    ]);
    let f_at_0 = sample_e4(1);
    let f_at_1 = sample_e4(2);
    let raw_half_input = sample_e4(3);
    assert_whir_fold_round_parity(seed, f_at_0, f_at_1, raw_half_input);
}

#[test]
fn whir_fold_round_update_parity_randomized() {
    let mut rng = rand::rng();
    for _ in 0..16 {
        let seed = Seed(std::array::from_fn(|_| rng.random()));
        let f_at_0 = sample_e4(rng.random());
        let f_at_1 = sample_e4(rng.random());
        let raw_half_input = sample_e4(rng.random());
        assert_whir_fold_round_parity(seed, f_at_0, f_at_1, raw_half_input);
    }
}

#[test]
fn whir_fold_round_update_parity_chained() {
    // Emulates multiple sequential fold rounds: the output seed of one
    // round becomes the input of the next. Catches state-propagation
    // mismatches that a single-round test would miss.
    let mut seed = Seed([0xcc; STATE_SIZE]);

    for round in 0..8u32 {
        let f_at_0 = sample_e4(round * 17 + 1);
        let f_at_1 = sample_e4(round * 19 + 2);
        let raw_half_input = sample_e4(round * 23 + 3);

        let (h_seed, h_coeffs, h_challenge) =
            host_whir_fold_round_update(seed, f_at_0, f_at_1, raw_half_input);
        let (d_seed, d_coeffs, d_challenge) =
            run_device_whir_fold_round_update(seed, f_at_0, f_at_1, raw_half_input);

        assert_eq!(d_seed.0, h_seed.0, "round {round}: seed");
        assert_eq!(d_coeffs, h_coeffs, "round {round}: coeffs");
        assert_eq!(d_challenge, h_challenge, "round {round}: challenge");

        seed = h_seed;
    }
}
claims_parity_suite!(
    babybear_claims,
    E4,
    sample_e4,
    crate::baby_bear::gkr_ops::backward_new_claims_two_var,
    crate::baby_bear::gkr_ops::backward_new_claims_linear,
    crate::baby_bear::gkr_ops::backward_dim_reducing_lsb_lines,
    crate::baby_bear::gkr_ops::build_combined_claim
);
