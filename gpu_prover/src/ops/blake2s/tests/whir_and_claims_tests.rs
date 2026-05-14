use era_cudart::memory::{memory_copy_async, DeviceAllocation};

use rand::Rng;

use super::super::*;
use crate::upstream::{Field, Seed};

fn sample_e4(seed: u32) -> E4 {
    use field::PrimeField;
    E4::from_array_of_base([
        BF::from_u32_with_reduction(seed.wrapping_mul(0x9E3779B1)),
        BF::from_u32_with_reduction(seed.wrapping_mul(0x85EBCA77)),
        BF::from_u32_with_reduction(seed.wrapping_mul(0xC2B2AE3D)),
        BF::from_u32_with_reduction(seed.wrapping_mul(0x27D4EB2F)),
    ])
}

/// Runs the exact host-side per-round callback logic and returns the
/// updated state plus the derived round coefficients and challenge.
fn host_backward_round_update(
    mut seed: Seed,
    mut claim: E4,
    mut eq_prefactor: E4,
    prev_coord: E4,
    e_partial: E4,
    c_partial: E4,
) -> (Seed, E4, E4, [E4; 4], E4) {
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
    use prover::gkr::sumcheck::{
        evaluate_eq_poly, evaluate_small_univariate_poly,
        output_univariate_monomial_form_max_quadratic,
    };

    let eq_prefactor_inv = eq_prefactor.inverse().expect("non-zero");
    let mut normalized_claim = claim;
    normalized_claim.mul_assign(&eq_prefactor_inv);

    let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E4>(
        prev_coord,
        normalized_claim,
        e_partial,
        c_partial,
    );
    commit_field_els::<BF, E4>(&mut seed, &coeffs);
    let challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
    claim = evaluate_small_univariate_poly::<BF, E4, 4>(&coeffs, &challenge);
    eq_prefactor = evaluate_eq_poly::<BF, E4>(&challenge, &prev_coord);
    (seed, claim, eq_prefactor, coeffs, challenge)
}

fn run_device_backward_round_update(
    seed_in: Seed,
    claim_in: E4,
    eq_prefactor_in: E4,
    prev_coord: E4,
    e_partial: E4,
    c_partial: E4,
) -> (Seed, E4, E4, [E4; 4], E4) {
    let stream = CudaStream::default();

    // Inputs.
    let mut d_reduction: DeviceAllocation<E4> = DeviceAllocation::alloc(2).unwrap();
    let mut d_prev_coord: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    memory_copy_async(&mut d_reduction, &[e_partial, c_partial], &stream).unwrap();
    memory_copy_async(&mut d_prev_coord, &[prev_coord], &stream).unwrap();

    // In/out state.
    let mut d_seed: DeviceAllocation<u32> = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    let mut d_claim: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    let mut d_eq_prefactor: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    memory_copy_async(&mut d_seed, &seed_in.0[..], &stream).unwrap();
    memory_copy_async(&mut d_claim, &[claim_in], &stream).unwrap();
    memory_copy_async(&mut d_eq_prefactor, &[eq_prefactor_in], &stream).unwrap();

    // Outputs.
    let mut d_coeffs: DeviceAllocation<E4> = DeviceAllocation::alloc(4).unwrap();
    let mut d_challenge: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();

    super::backward_sumcheck_round_update(
        &d_reduction,
        &d_prev_coord,
        &mut d_seed,
        &mut d_claim,
        &mut d_eq_prefactor,
        &mut d_coeffs,
        &mut d_challenge,
        &stream,
    )
    .unwrap();

    let mut seed_out = Seed::default();
    let mut claim_out = [E4::ZERO];
    let mut eq_prefactor_out = [E4::ZERO];
    let mut coeffs_out = [E4::ZERO; 4];
    let mut challenge_out = [E4::ZERO];
    memory_copy_async(&mut seed_out.0[..], &d_seed, &stream).unwrap();
    memory_copy_async(&mut claim_out[..], &d_claim, &stream).unwrap();
    memory_copy_async(&mut eq_prefactor_out[..], &d_eq_prefactor, &stream).unwrap();
    memory_copy_async(&mut coeffs_out[..], &d_coeffs, &stream).unwrap();
    memory_copy_async(&mut challenge_out[..], &d_challenge, &stream).unwrap();
    stream.synchronize().unwrap();

    (
        seed_out,
        claim_out[0],
        eq_prefactor_out[0],
        coeffs_out,
        challenge_out[0],
    )
}

fn assert_backward_round_parity(
    seed_in: Seed,
    claim_in: E4,
    eq_prefactor_in: E4,
    prev_coord: E4,
    e_partial: E4,
    c_partial: E4,
) {
    let (h_seed, h_claim, h_eq, h_coeffs, h_challenge) = host_backward_round_update(
        seed_in,
        claim_in,
        eq_prefactor_in,
        prev_coord,
        e_partial,
        c_partial,
    );
    let (d_seed, d_claim, d_eq, d_coeffs, d_challenge) = run_device_backward_round_update(
        seed_in,
        claim_in,
        eq_prefactor_in,
        prev_coord,
        e_partial,
        c_partial,
    );
    assert_eq!(d_seed.0, h_seed.0, "seed mismatch");
    assert_eq!(d_coeffs, h_coeffs, "coeffs mismatch");
    assert_eq!(d_challenge, h_challenge, "challenge mismatch");
    assert_eq!(d_claim, h_claim, "claim mismatch");
    assert_eq!(d_eq, h_eq, "eq_prefactor mismatch");
}

#[test]
fn backward_round_update_parity_fixed() {
    let seed = Seed([
        0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555, 0x66666666, 0x77777777,
        0x88888888,
    ]);
    let claim = sample_e4(1);
    let eq_prefactor = sample_e4(2);
    let prev_coord = sample_e4(3);
    let e_partial = sample_e4(4);
    let c_partial = sample_e4(5);
    assert_backward_round_parity(seed, claim, eq_prefactor, prev_coord, e_partial, c_partial);
}

#[test]
fn backward_round_update_parity_randomized() {
    let mut rng = rand::rng();
    for _ in 0..16 {
        let seed = Seed(std::array::from_fn(|_| rng.random()));
        let claim = sample_e4(rng.random());
        let eq_prefactor = sample_e4(rng.random::<u32>() | 1); // avoid zero
        let prev_coord = sample_e4(rng.random::<u32>() | 1); // prev_coord is also used as a_plus_b, must be non-zero
        let e_partial = sample_e4(rng.random());
        let c_partial = sample_e4(rng.random());
        assert_backward_round_parity(seed, claim, eq_prefactor, prev_coord, e_partial, c_partial);
    }
}

// -----------------------------------------------------------------------
// Fused WHIR fold round-update kernel parity test.
//
// Mirrors the host per-round callback in whir_fold.rs:schedule_fold_round
// and checks that the device kernel produces bit-exact state updates: new
// seed, coefficients, challenge.
// -----------------------------------------------------------------------

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
        for (dst, coeff) in result.iter_mut().zip(coeffs.into_iter()) {
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
    commit_field_els::<BF, E4>(&mut seed, &coeffs);
    let challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
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

    super::whir_fold_round_update(
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

// -----------------------------------------------------------------------
// Assemble-query-indexes kernel parity test.
//
// Mirrors `draw_query_bits_after_verified_pow` + `BitSource` +
// `assemble_query_index` chain: the kernel consumes the squeezed random
// buffer and produces query indexes matching the host reference.
// -----------------------------------------------------------------------

fn host_assemble_query_indexes(
    raw_bits: &[u32],
    num_queries: usize,
    log_domain_size: usize,
) -> Vec<u32> {
    use prover::query_utils::{assemble_query_index, BitSource};

    // Host path: skip the first word (PoW header), then assemble LE.
    let source_after_skip = raw_bits[1..].to_vec();
    let mut bit_source = BitSource::new(source_after_skip);
    (0..num_queries)
        .map(|_| assemble_query_index(log_domain_size, &mut bit_source) as u32)
        .collect()
}

fn assert_assemble_query_indexes_parity(
    raw_bits: &[u32],
    num_queries: usize,
    log_domain_size: u32,
) {
    let expected = host_assemble_query_indexes(raw_bits, num_queries, log_domain_size as usize);

    let stream = CudaStream::default();
    let mut d_raw: DeviceAllocation<u32> = DeviceAllocation::alloc(raw_bits.len()).unwrap();
    let mut d_indexes: DeviceAllocation<u32> = DeviceAllocation::alloc(num_queries).unwrap();
    memory_copy_async(&mut d_raw, raw_bits, &stream).unwrap();
    super::assemble_query_indexes(&d_raw, &mut d_indexes, log_domain_size, &stream).unwrap();

    let mut actual = vec![0u32; num_queries];
    memory_copy_async(&mut actual, &d_indexes, &stream).unwrap();
    stream.synchronize().unwrap();

    assert_eq!(actual, expected);
}

#[test]
fn assemble_query_indexes_parity_small() {
    // 4 queries, 8-bit domain: 32 + 4*8 = 64 bits = 2 words (pad to 8 for
    // squeeze alignment).
    let raw_bits: Vec<u32> = (0..8).map(|i| 0xDEADBEEFu32.wrapping_mul(i + 1)).collect();
    assert_assemble_query_indexes_parity(&raw_bits, 4, 8);
}

#[test]
fn assemble_query_indexes_parity_realistic() {
    // Matches a typical WHIR round: ~32-64 queries with ~20-24-bit domain.
    let mut rng = rand::rng();
    for &(num_queries, log_domain_size) in
        &[(32usize, 24u32), (48, 20), (64, 16), (16, 30), (1, 24)]
    {
        // Pad to multiple of 8 (squeeze output granularity).
        let bits_needed = 32 + num_queries * log_domain_size as usize;
        let words_needed = bits_needed.div_ceil(32);
        let padded_words = words_needed.next_multiple_of(STATE_SIZE);
        let raw_bits: Vec<u32> = (0..padded_words).map(|_| rng.random()).collect();
        assert_assemble_query_indexes_parity(&raw_bits, num_queries, log_domain_size);
    }
}

#[test]
fn backward_round_update_parity_chained() {
    // Emulates multiple sequential rounds: the output seed/claim/eq of one
    // round becomes the input of the next. This catches state-propagation
    // mismatches that a single-round test would miss.
    let mut seed = Seed([0xaa; STATE_SIZE]);
    let mut claim = sample_e4(100);
    let mut eq_prefactor = sample_e4(200);

    for round in 0..8u32 {
        let prev_coord = sample_e4(round * 7 + 1);
        let e_partial = sample_e4(round * 11 + 3);
        let c_partial = sample_e4(round * 13 + 5);

        let (h_seed, h_claim, h_eq, h_coeffs, h_challenge) =
            host_backward_round_update(seed, claim, eq_prefactor, prev_coord, e_partial, c_partial);
        let (d_seed, d_claim, d_eq, d_coeffs, d_challenge) = run_device_backward_round_update(
            seed,
            claim,
            eq_prefactor,
            prev_coord,
            e_partial,
            c_partial,
        );

        assert_eq!(d_seed.0, h_seed.0, "round {round}: seed");
        assert_eq!(d_coeffs, h_coeffs, "round {round}: coeffs");
        assert_eq!(d_challenge, h_challenge, "round {round}: challenge");
        assert_eq!(d_claim, h_claim, "round {round}: claim");
        assert_eq!(d_eq, h_eq, "round {round}: eq_prefactor");

        seed = h_seed;
        claim = h_claim;
        eq_prefactor = h_eq;
    }
}

// -----------------------------------------------------------------------
// Per-address backward new_claims evaluator parity tests.
//
// `backward_new_claims_two_var` must match the host
// `evaluate_with_two_variable_eq_ext(values, r_before_last, r_last)`.
// `backward_new_claims_linear` must match the host
// `interpolate_linear(f0, f1, last_r)`. Both kernels are called once per
// layer boundary in the backward pass and produce `num_addresses` E4s.
// -----------------------------------------------------------------------

fn host_new_claim_two_var(values: &[E4; 4], r_before_last: E4, r_last: E4) -> E4 {
    let mut result = E4::ZERO;
    let mut w00 = E4::ONE;
    w00.sub_assign(&r_before_last);
    let mut tmp = E4::ONE;
    tmp.sub_assign(&r_last);
    w00.mul_assign(&tmp);
    let mut term = values[0];
    term.mul_assign(&w00);
    result.add_assign(&term);

    let mut w01 = E4::ONE;
    w01.sub_assign(&r_before_last);
    w01.mul_assign(&r_last);
    let mut term = values[1];
    term.mul_assign(&w01);
    result.add_assign(&term);

    let mut w10 = r_before_last;
    let mut tmp = E4::ONE;
    tmp.sub_assign(&r_last);
    w10.mul_assign(&tmp);
    let mut term = values[2];
    term.mul_assign(&w10);
    result.add_assign(&term);

    let mut w11 = r_before_last;
    w11.mul_assign(&r_last);
    let mut term = values[3];
    term.mul_assign(&w11);
    result.add_assign(&term);
    result
}

fn host_new_claim_linear(f0: E4, f1: E4, r: E4) -> E4 {
    let mut result = f1;
    result.sub_assign(&f0);
    result.mul_assign(&r);
    result.add_assign(&f0);
    result
}

fn run_device_new_claims_two_var(packed_values: &[E4], r_before_last: E4, r_last: E4) -> Vec<E4> {
    let stream = CudaStream::default();
    let num_addresses = packed_values.len() / 4;
    let mut d_packed: DeviceAllocation<E4> = DeviceAllocation::alloc(packed_values.len()).unwrap();
    memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
    let mut d_challenges: DeviceAllocation<E4> = DeviceAllocation::alloc(2).unwrap();
    memory_copy_async(&mut d_challenges, &[r_before_last, r_last], &stream).unwrap();
    let mut d_out: DeviceAllocation<E4> = DeviceAllocation::alloc(num_addresses).unwrap();
    super::backward_new_claims_two_var(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
    let mut out = vec![E4::ZERO; num_addresses];
    memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
    stream.synchronize().unwrap();
    out
}

fn run_device_new_claims_linear(packed_values: &[E4], last_r: E4) -> Vec<E4> {
    let stream = CudaStream::default();
    let num_addresses = packed_values.len() / 2;
    let mut d_packed: DeviceAllocation<E4> = DeviceAllocation::alloc(packed_values.len()).unwrap();
    memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
    let mut d_challenges: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    memory_copy_async(&mut d_challenges, &[last_r], &stream).unwrap();
    let mut d_out: DeviceAllocation<E4> = DeviceAllocation::alloc(num_addresses).unwrap();
    super::backward_new_claims_linear(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
    let mut out = vec![E4::ZERO; num_addresses];
    memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
    stream.synchronize().unwrap();
    out
}

#[test]
fn backward_new_claims_two_var_parity_fixed() {
    let r_before_last = sample_e4(17);
    let r_last = sample_e4(23);
    let num_addresses = 7usize;
    let mut packed = Vec::with_capacity(num_addresses * 4);
    for i in 0..num_addresses * 4 {
        packed.push(sample_e4(100 + i as u32));
    }
    let device = run_device_new_claims_two_var(&packed, r_before_last, r_last);
    for i in 0..num_addresses {
        let v: [E4; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
        let host = host_new_claim_two_var(&v, r_before_last, r_last);
        assert_eq!(device[i], host, "address {i} mismatch");
    }
}

#[test]
fn backward_new_claims_two_var_parity_randomized() {
    use rand::Rng;
    let mut rng = rand::rng();
    for num_addresses in [1usize, 2, 3, 8, 17, 64, 257] {
        let r_before_last = sample_e4(rng.random::<u32>());
        let r_last = sample_e4(rng.random::<u32>());
        let packed: Vec<E4> = (0..num_addresses * 4)
            .map(|_| sample_e4(rng.random::<u32>()))
            .collect();
        let device = run_device_new_claims_two_var(&packed, r_before_last, r_last);
        for i in 0..num_addresses {
            let v: [E4; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
            let host = host_new_claim_two_var(&v, r_before_last, r_last);
            assert_eq!(device[i], host, "N={num_addresses} addr {i} mismatch");
        }
    }
}

#[test]
fn backward_new_claims_linear_parity_fixed() {
    let last_r = sample_e4(31);
    let num_addresses = 5usize;
    let mut packed = Vec::with_capacity(num_addresses * 2);
    for i in 0..num_addresses * 2 {
        packed.push(sample_e4(200 + i as u32));
    }
    let device = run_device_new_claims_linear(&packed, last_r);
    for i in 0..num_addresses {
        let f0 = packed[i * 2];
        let f1 = packed[i * 2 + 1];
        let host = host_new_claim_linear(f0, f1, last_r);
        assert_eq!(device[i], host, "address {i} mismatch");
    }
}

#[test]
fn backward_new_claims_linear_parity_randomized() {
    use rand::Rng;
    let mut rng = rand::rng();
    for num_addresses in [1usize, 2, 3, 8, 17, 64, 257] {
        let last_r = sample_e4(rng.random::<u32>());
        let packed: Vec<E4> = (0..num_addresses * 2)
            .map(|_| sample_e4(rng.random::<u32>()))
            .collect();
        let device = run_device_new_claims_linear(&packed, last_r);
        for i in 0..num_addresses {
            let f0 = packed[i * 2];
            let f1 = packed[i * 2 + 1];
            let host = host_new_claim_linear(f0, f1, last_r);
            assert_eq!(device[i], host, "N={num_addresses} addr {i} mismatch");
        }
    }
}

fn host_combined_claim(claims: &[E4], batching: E4, exp_idx: &[(u32, u32)]) -> E4 {
    let mut result = E4::ZERO;
    for (exp, idx) in exp_idx {
        let mut pow = E4::ONE;
        for _ in 0..*exp {
            pow.mul_assign(&batching);
        }
        let mut term = claims[*idx as usize];
        term.mul_assign(&pow);
        result.add_assign(&term);
    }
    result
}

fn run_device_combined_claim(claims: &[E4], batching: E4, exp_idx: &[(u32, u32)]) -> (E4, E4) {
    let stream = CudaStream::default();
    let mut d_claims: DeviceAllocation<E4> = DeviceAllocation::alloc(claims.len()).unwrap();
    memory_copy_async(&mut d_claims, claims, &stream).unwrap();
    let mut d_batching: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    memory_copy_async(&mut d_batching, &[batching], &stream).unwrap();
    let desc_flat: Vec<u32> = exp_idx.iter().flat_map(|(exp, idx)| [*exp, *idx]).collect();
    let mut d_claim_out: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    let mut d_eq_out: DeviceAllocation<E4> = DeviceAllocation::alloc(1).unwrap();
    super::build_combined_claim(
        &d_claims,
        &d_batching,
        &desc_flat,
        &mut d_claim_out,
        &mut d_eq_out,
        &stream,
    )
    .unwrap();
    let mut claim_out = [E4::ZERO];
    let mut eq_out = [E4::ZERO];
    memory_copy_async(&mut claim_out[..], &d_claim_out, &stream).unwrap();
    memory_copy_async(&mut eq_out[..], &d_eq_out, &stream).unwrap();
    stream.synchronize().unwrap();
    (claim_out[0], eq_out[0])
}

#[test]
fn build_combined_claim_parity_fixed() {
    let claims: Vec<E4> = (0..6usize).map(|idx| sample_e4(500 + idx as u32)).collect();
    let batching = sample_e4(999);
    let exp_idx = vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)];
    let (device_claim, device_eq) = run_device_combined_claim(&claims, batching, &exp_idx);
    let host_claim = host_combined_claim(&claims, batching, &exp_idx);
    assert_eq!(device_claim, host_claim, "combined-claim mismatch");
    assert_eq!(device_eq, E4::ONE, "eq-prefactor must be ONE");
}

#[test]
fn build_combined_claim_parity_randomized() {
    use rand::Rng;
    let mut rng = rand::rng();
    for _ in 0..8 {
        let num_claims = rng.random_range(1usize..=40);
        let num_terms = rng.random_range(1usize..=50);
        let claims: Vec<E4> = (0..num_claims)
            .map(|_| sample_e4(rng.random::<u32>()))
            .collect();
        let batching = sample_e4(rng.random::<u32>());
        let exp_idx: Vec<(u32, u32)> = (0..num_terms)
            .map(|_| {
                let exp = rng.random_range(0u32..=40);
                let idx = rng.random_range(0..num_claims as u32);
                (exp, idx)
            })
            .collect();
        let (device_claim, device_eq) = run_device_combined_claim(&claims, batching, &exp_idx);
        let host_claim = host_combined_claim(&claims, batching, &exp_idx);
        assert_eq!(
            device_claim, host_claim,
            "random combined-claim mismatch (N_claims={num_claims}, N_terms={num_terms})"
        );
        assert_eq!(device_eq, E4::ONE);
    }
}
