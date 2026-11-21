use era_cudart::{
    memory::{memory_copy_async, DeviceAllocation},
    stream::CudaStream,
};
use gpu_hash::blake2s::STATE_SIZE;
use rand::Rng;

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

// -----------------------------------------------------------------------
// Per-address backward new_claims evaluator parity tests.
//
// `backward_new_claims_two_var` must match the host
// `evaluate_with_two_variable_eq_ext(values, r_before_last, r_last)`.
// `backward_new_claims_linear` must match the host
// `interpolate_linear(f0, f1, last_r)`. Both kernels are called once per
// layer boundary in the backward pass and produce `num_addresses` E4s.
// -----------------------------------------------------------------------

// One parity suite instantiated for each field's thin launchers.
macro_rules! claims_parity_suite {
    ($module:ident, $field:ty, $sample:path, $two_var:path, $linear:path, $lsb:path, $combined:path) => {
        mod $module {
            use super::*;
            type F = $field;
            use $two_var as launch_two_var;
            use $linear as launch_linear;
            use $lsb as launch_lsb_lines;
            use $combined as launch_combined;
            fn sample(seed: u32) -> F {
                $sample(seed)
            }
            fn host_new_claim_two_var(values: &[F; 4], r_before_last: F, r_last: F) -> F {
                let mut result = F::ZERO;
                let mut w00 = F::ONE;
                w00.sub_assign(&r_before_last);
                let mut tmp = F::ONE;
                tmp.sub_assign(&r_last);
                w00.mul_assign(&tmp);
                let mut term = values[0];
                term.mul_assign(&w00);
                result.add_assign(&term);

                let mut w01 = F::ONE;
                w01.sub_assign(&r_before_last);
                w01.mul_assign(&r_last);
                let mut term = values[1];
                term.mul_assign(&w01);
                result.add_assign(&term);

                let mut w10 = r_before_last;
                let mut tmp = F::ONE;
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

            fn host_new_claim_linear(f0: F, f1: F, r: F) -> F {
                let mut result = f1;
                result.sub_assign(&f0);
                result.mul_assign(&r);
                result.add_assign(&f0);
                result
            }

            fn run_device_new_claims_two_var(packed_values: &[F], r_before_last: F, r_last: F) -> Vec<F> {
                let stream = CudaStream::default();
                let num_addresses = packed_values.len() / 4;
                let mut d_packed: DeviceAllocation<F> =
                    DeviceAllocation::alloc(packed_values.len()).unwrap();
                memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
                let mut d_challenges: DeviceAllocation<F> = DeviceAllocation::alloc(2).unwrap();
                memory_copy_async(&mut d_challenges, &[r_before_last, r_last], &stream).unwrap();
                let mut d_out: DeviceAllocation<F> = DeviceAllocation::alloc(num_addresses).unwrap();
                launch_two_var(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
                let mut out = vec![F::ZERO; num_addresses];
                memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
                stream.synchronize().unwrap();
                out
            }

            fn run_device_new_claims_linear(packed_values: &[F], last_r: F) -> Vec<F> {
                let stream = CudaStream::default();
                let num_addresses = packed_values.len() / 2;
                let mut d_packed: DeviceAllocation<F> =
                    DeviceAllocation::alloc(packed_values.len()).unwrap();
                memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
                let mut d_challenges: DeviceAllocation<F> = DeviceAllocation::alloc(1).unwrap();
                memory_copy_async(&mut d_challenges, &[last_r], &stream).unwrap();
                let mut d_out: DeviceAllocation<F> = DeviceAllocation::alloc(num_addresses).unwrap();
                launch_linear(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
                let mut out = vec![F::ZERO; num_addresses];
                memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
                stream.synchronize().unwrap();
                out
            }

            #[test]
            fn backward_new_claims_two_var_parity_fixed() {
                let r_before_last = sample(17);
                let r_last = sample(23);
                let num_addresses = 7usize;
                let mut packed = Vec::with_capacity(num_addresses * 4);
                for i in 0..num_addresses * 4 {
                    packed.push(sample(100 + i as u32));
                }
                let device = run_device_new_claims_two_var(&packed, r_before_last, r_last);
                for i in 0..num_addresses {
                    let v: [F; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
                    let host = host_new_claim_two_var(&v, r_before_last, r_last);
                    assert_eq!(device[i], host, "address {i} mismatch");
                }
            }

            #[test]
            fn backward_new_claims_two_var_parity_randomized() {
                use rand::Rng;
                let mut rng = rand::rng();
                for num_addresses in [1usize, 2, 3, 8, 17, 64, 257] {
                    let r_before_last = sample(rng.random::<u32>());
                    let r_last = sample(rng.random::<u32>());
                    let packed: Vec<F> = (0..num_addresses * 4)
                        .map(|_| sample(rng.random::<u32>()))
                        .collect();
                    let device = run_device_new_claims_two_var(&packed, r_before_last, r_last);
                    for i in 0..num_addresses {
                        let v: [F; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
                        let host = host_new_claim_two_var(&v, r_before_last, r_last);
                        assert_eq!(device[i], host, "N={num_addresses} addr {i} mismatch");
                    }
                }
            }

            #[test]
            fn backward_new_claims_linear_parity_fixed() {
                let last_r = sample(31);
                let num_addresses = 5usize;
                let mut packed = Vec::with_capacity(num_addresses * 2);
                for i in 0..num_addresses * 2 {
                    packed.push(sample(200 + i as u32));
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
                    let last_r = sample(rng.random::<u32>());
                    let packed: Vec<F> = (0..num_addresses * 2)
                        .map(|_| sample(rng.random::<u32>()))
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

            // `backward_dim_reducing_lsb_lines` must match the host dim-reducing
            // final-round reduction: out[0] = interpolate_linear(evals[0], evals[2], rbl),
            // out[1] = interpolate_linear(evals[1], evals[3], rbl). The two LSB lines are
            // what the prover commits to the transcript and sends in the proof.
            fn run_device_lsb_lines(packed_values: &[F], r_before_last: F) -> Vec<F> {
                let stream = CudaStream::default();
                let num_addresses = packed_values.len() / 4;
                let mut d_packed: DeviceAllocation<F> =
                    DeviceAllocation::alloc(packed_values.len()).unwrap();
                memory_copy_async(&mut d_packed, packed_values, &stream).unwrap();
                let mut d_challenges: DeviceAllocation<F> = DeviceAllocation::alloc(1).unwrap();
                memory_copy_async(&mut d_challenges, &[r_before_last], &stream).unwrap();
                let mut d_out: DeviceAllocation<F> = DeviceAllocation::alloc(num_addresses * 2).unwrap();
                launch_lsb_lines(&d_packed, &d_challenges, &mut d_out, &stream).unwrap();
                let mut out = vec![F::ZERO; num_addresses * 2];
                memory_copy_async(&mut out[..], &d_out, &stream).unwrap();
                stream.synchronize().unwrap();
                out
            }

            #[test]
            fn backward_dim_reducing_lsb_lines_parity_fixed() {
                let r_before_last = sample(41);
                let num_addresses = 6usize;
                let packed: Vec<F> = (0..num_addresses * 4)
                    .map(|i| sample(300 + i as u32))
                    .collect();
                let device = run_device_lsb_lines(&packed, r_before_last);
                for i in 0..num_addresses {
                    let v: [F; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
                    let lsb0 = host_new_claim_linear(v[0], v[2], r_before_last);
                    let lsb1 = host_new_claim_linear(v[1], v[3], r_before_last);
                    assert_eq!(device[i * 2], lsb0, "address {i} lsb0 mismatch");
                    assert_eq!(device[i * 2 + 1], lsb1, "address {i} lsb1 mismatch");
                }
            }

            #[test]
            fn backward_dim_reducing_lsb_lines_parity_randomized() {
                use rand::Rng;
                let mut rng = rand::rng();
                for num_addresses in [1usize, 2, 3, 8, 17, 64, 257] {
                    let r_before_last = sample(rng.random::<u32>());
                    let packed: Vec<F> = (0..num_addresses * 4)
                        .map(|_| sample(rng.random::<u32>()))
                        .collect();
                    let device = run_device_lsb_lines(&packed, r_before_last);
                    for i in 0..num_addresses {
                        let v: [F; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
                        let lsb0 = host_new_claim_linear(v[0], v[2], r_before_last);
                        let lsb1 = host_new_claim_linear(v[1], v[3], r_before_last);
                        assert_eq!(
                            device[i * 2],
                            lsb0,
                            "N={num_addresses} addr {i} lsb0 mismatch"
                        );
                        assert_eq!(
                            device[i * 2 + 1],
                            lsb1,
                            "N={num_addresses} addr {i} lsb1 mismatch"
                        );
                    }
                }
            }

            // Cross-check: lerp over LSB of the two lines at r_last must reproduce the full
            // two-var new_claim — i.e. the LSB-line split + linear new_claim is consistent
            // with the two-variable reference `host_new_claim_two_var` (and so with the CPU
            // final claim).
            #[test]
            fn lsb_lines_then_linear_matches_two_var() {
                let rbl = sample(71);
                let r_last = sample(89);
                let num_addresses = 4usize;
                let packed: Vec<F> = (0..num_addresses * 4)
                    .map(|i| sample(400 + i as u32))
                    .collect();
                let lines = run_device_lsb_lines(&packed, rbl);
                let claims = run_device_new_claims_linear(&lines, r_last);
                for i in 0..num_addresses {
                    let v: [F; 4] = packed[i * 4..i * 4 + 4].try_into().unwrap();
                    let expected = host_new_claim_two_var(&v, rbl, r_last);
                    assert_eq!(claims[i], expected, "address {i} composed mismatch");
                }
            }

            fn host_combined_claim(claims: &[F], batching: F, exp_idx: &[(u32, u32)]) -> F {
                let mut result = F::ZERO;
                for (exp, idx) in exp_idx {
                    let mut pow = F::ONE;
                    for _ in 0..*exp {
                        pow.mul_assign(&batching);
                    }
                    let mut term = claims[*idx as usize];
                    term.mul_assign(&pow);
                    result.add_assign(&term);
                }
                result
            }

            fn run_device_combined_claim(claims: &[F], batching: F, exp_idx: &[(u32, u32)]) -> (F, F) {
                let stream = CudaStream::default();
                let mut d_claims: DeviceAllocation<F> = DeviceAllocation::alloc(claims.len()).unwrap();
                memory_copy_async(&mut d_claims, claims, &stream).unwrap();
                let mut d_batching: DeviceAllocation<F> = DeviceAllocation::alloc(1).unwrap();
                memory_copy_async(&mut d_batching, &[batching], &stream).unwrap();
                let desc_flat: Vec<u32> = exp_idx.iter().flat_map(|(exp, idx)| [*exp, *idx]).collect();
                let mut d_claim_out: DeviceAllocation<F> = DeviceAllocation::alloc(1).unwrap();
                let mut d_eq_out: DeviceAllocation<F> = DeviceAllocation::alloc(1).unwrap();
                launch_combined(
                    &d_claims,
                    &d_batching,
                    &desc_flat,
                    &mut d_claim_out,
                    &mut d_eq_out,
                    &stream,
                )
                .unwrap();
                let mut claim_out = [F::ZERO];
                let mut eq_out = [F::ZERO];
                memory_copy_async(&mut claim_out[..], &d_claim_out, &stream).unwrap();
                memory_copy_async(&mut eq_out[..], &d_eq_out, &stream).unwrap();
                stream.synchronize().unwrap();
                (claim_out[0], eq_out[0])
            }

            #[test]
            fn build_combined_claim_parity_fixed() {
                let claims: Vec<F> = (0..6usize).map(|idx| sample(500 + idx as u32)).collect();
                let batching = sample(999);
                let exp_idx = vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)];
                let (device_claim, device_eq) = run_device_combined_claim(&claims, batching, &exp_idx);
                let host_claim = host_combined_claim(&claims, batching, &exp_idx);
                assert_eq!(device_claim, host_claim, "combined-claim mismatch");
                assert_eq!(device_eq, F::ONE, "eq-prefactor must be ONE");
            }

            #[test]
            fn build_combined_claim_parity_randomized() {
                use rand::Rng;
                let mut rng = rand::rng();
                for _ in 0..8 {
                    let num_claims = rng.random_range(1usize..=40);
                    let num_terms = rng.random_range(1usize..=50);
                    let claims: Vec<F> = (0..num_claims)
                        .map(|_| sample(rng.random::<u32>()))
                        .collect();
                    let batching = sample(rng.random::<u32>());
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
                    assert_eq!(device_eq, F::ONE);
                }
            }

            #[test]
            fn build_combined_claim_empty_and_zero_batching() {
                let claims = [sample(5), sample(17), sample(31)];
                for batching in [F::ZERO, F::ONE, sample(99)] {
                    for terms in [vec![], vec![(3, 0), (0, 1), (3, 2), (1, 0), (0, 2)]] {
                        let (actual, eq) = run_device_combined_claim(&claims, batching, &terms);
                        assert_eq!(actual, host_combined_claim(&claims, batching, &terms));
                        assert_eq!(eq, F::ONE);
                    }
                }
            }

            #[test]
            fn build_combined_claim_full_exponent_range() {
                // The CPU Field implementation is independent of the CUDA e4 helper
                // and of the descriptor traversal.
                let claims = [sample(5), sample(17), sample(31)];
                let sparse = vec![
                    (u32::MAX, 0),
                    (0, 1),
                    (31, 2),
                    (1 << 31, 0),
                    (u32::MAX - 1, 1),
                    (31, 1),
                    (0, 0),
                ];
                let full: Vec<(u32, u32)> = (0..crate::gkr_ops::GKR_COMBINED_CLAIM_MAX_PAIRS)
                    .map(|i| ((i as u32).wrapping_mul(0x9e3779b1), (i % 3) as u32))
                    .collect();
                for batching in [F::ZERO, F::ONE, sample(99)] {
                    for terms in [&[][..], sparse.as_slice(), full.as_slice()] {
                        let mut expected = F::ZERO;
                        for &(exp, index) in terms {
                            let mut term = batching.pow(exp);
                            term.mul_assign(&claims[index as usize]);
                            expected.add_assign(&term);
                        }
                        let (actual, eq) = run_device_combined_claim(&claims, batching, terms);
                        assert_eq!(actual, expected);
                        assert_eq!(eq, F::ONE);
                    }
                }
            }

            #[test]
            fn build_combined_claim_reduction_boundaries() {
                let claims: Vec<F> = (0..37).map(|i| sample(1000 + i)).collect();
                // Cover partial warps, the block boundary and a final partial strided pass.
                // Exponents repeat in non-monotone order; claim indices repeat independently.
                for count in [31usize, 32, 33, 255, 256, 257, 513] {
                    let terms: Vec<(u32, u32)> = (0..count)
                        .map(|i| {
                            (
                                ((i * 17 + 9) % 41) as u32,
                                ((i * 13 + 5) % claims.len()) as u32,
                            )
                        })
                        .collect();
                    for batching in [F::ZERO, F::ONE, sample(1234)] {
                        let (actual, prefactor) = run_device_combined_claim(&claims, batching, &terms);
                        assert_eq!(
                            actual,
                            host_combined_claim(&claims, batching, &terms),
                            "terms={count}"
                        );
                        assert_eq!(prefactor, F::ONE);
                    }
                }
            }
        }
    };
}

pub(crate) use claims_parity_suite;
