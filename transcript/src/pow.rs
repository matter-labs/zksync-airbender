use super::*;
use worker::Worker;

const BLAKE2S_NO_RESULT: u64 = u64::MAX;
const BLAKE2S_ROUNDS_PER_INVOCAITON: usize = 1 << 16u32;

impl Blake2sTranscript {
    pub fn search_pow(seed: &Seed, pow_bits: u32, worker: &Worker) -> (Seed, u64) {
        assert!(pow_bits <= 32);

        let (initial_state, base_input) = Self::prepare_pow_search(seed);

        if pow_bits <= BLAKE2S_ROUNDS_PER_INVOCAITON.trailing_zeros() {
            return Self::search_pow_serial_from_prepared(
                seed,
                pow_bits,
                initial_state,
                base_input,
            );
        }

        Self::search_pow_parallel_from_prepared(seed, pow_bits, worker, initial_state, base_input)
    }

    fn prepare_pow_search(
        seed: &Seed,
    ) -> (
        [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    ) {
        let initial_state = [
            CONFIGURED_IV[0],
            CONFIGURED_IV[1],
            CONFIGURED_IV[2],
            CONFIGURED_IV[3],
            CONFIGURED_IV[4],
            CONFIGURED_IV[5],
            CONFIGURED_IV[6],
            CONFIGURED_IV[7],
            IV[0],
            IV[1],
            IV[2],
            IV[3],
            IV[4] ^ (((BLAKE2S_DIGEST_SIZE_U32_WORDS + 2) * core::mem::size_of::<u32>()) as u32),
            IV[5],
            IV[6] ^ 0xffffffff,
            IV[7],
        ];

        let mut base_input = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        base_input[..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(&seed.0);

        (initial_state, base_input)
    }

    fn search_pow_serial_from_prepared(
        seed: &Seed,
        pow_bits: u32,
        initial_state: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        base_input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    ) -> (Seed, u64) {
        let threshold = u32::MAX.checked_shr(pow_bits).unwrap_or(0);
        let mut input = base_input;
        for challenge in 0u64..(BLAKE2S_NO_RESULT - 1) {
            if Self::pow_challenge_matches(&mut input, &initial_state, challenge, threshold) {
                return Self::finalize_pow_result(seed, challenge, pow_bits);
            }
        }

        unreachable!("PoW search exhausted the nonce space without a result");
    }

    fn search_pow_parallel_from_prepared(
        seed: &Seed,
        pow_bits: u32,
        worker: &Worker,
        initial_state: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        base_input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    ) -> (Seed, u64) {
        use std::sync::atomic::AtomicU64;
        use std::sync::atomic::Ordering;

        let result = std::sync::Arc::new(AtomicU64::new(BLAKE2S_NO_RESULT));
        let threshold = u32::MAX.checked_shr(pow_bits).unwrap_or(0);
        let pow_rounds_per_invocation = BLAKE2S_ROUNDS_PER_INVOCAITON as u64;
        let num_workers = worker.num_cores as u64;

        worker.scope(usize::MAX, |scope, _| {
            for worker_idx in 0..num_workers {
                let mut input = base_input;
                let result = std::sync::Arc::clone(&result);
                Worker::smart_spawn(scope, worker_idx == num_workers - 1, move |_| {
                    for round_idx in
                        0..((BLAKE2S_NO_RESULT - 1) / num_workers / pow_rounds_per_invocation)
                    {
                        let base =
                            (worker_idx + round_idx * num_workers) * pow_rounds_per_invocation;

                        #[cfg(feature = "deterministic_pow")]
                        if result.load(Ordering::Relaxed) <= base {
                            break;
                        }
                        #[cfg(not(feature = "deterministic_pow"))]
                        if result.load(Ordering::Relaxed) != BLAKE2S_NO_RESULT {
                            break;
                        }

                        let rounds_this_invocation =
                            pow_rounds_per_invocation.min((BLAKE2S_NO_RESULT - 1) - base);
                        for j in 0..rounds_this_invocation {
                            let challenge_u64 = base + j;
                            if Self::pow_challenge_matches(
                                &mut input,
                                &initial_state,
                                challenge_u64,
                                threshold,
                            ) {
                                #[cfg(feature = "deterministic_pow")]
                                result.fetch_min(challenge_u64, Ordering::Relaxed);
                                #[cfg(not(feature = "deterministic_pow"))]
                                let _ = result.compare_exchange(
                                    BLAKE2S_NO_RESULT,
                                    challenge_u64,
                                    Ordering::Relaxed,
                                    Ordering::Relaxed,
                                );
                                return;
                            }
                        }
                    }
                })
            }
        });

        let challenge_u64 = result.load(Ordering::Relaxed);
        Self::finalize_pow_result(seed, challenge_u64, pow_bits)
    }

    #[inline(always)]
    fn pow_challenge_matches(
        input: &mut [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        initial_state: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        challenge_u64: u64,
        threshold: u32,
    ) -> bool {
        input[BLAKE2S_DIGEST_SIZE_U32_WORDS] = challenge_u64 as u32;
        input[BLAKE2S_DIGEST_SIZE_U32_WORDS + 1] = (challenge_u64 >> 32) as u32;
        let mut state = *initial_state;
        if USE_REDUCED_BLAKE2_ROUNDS {
            round_function_reduced_rounds(&mut state, input);
        } else {
            round_function_full_rounds(&mut state, input);
        }

        let word_to_test = CONFIGURED_IV[0] ^ state[0] ^ state[8];
        word_to_test <= threshold
    }

    fn finalize_pow_result(seed: &Seed, challenge_u64: u64, pow_bits: u32) -> (Seed, u64) {
        let mut new_seed = *seed;
        Self::verify_pow(&mut new_seed, challenge_u64, pow_bits);
        (new_seed, challenge_u64)
    }
}

#[cfg(all(test, feature = "deterministic_pow"))]
mod tests {
    use super::*;

    fn test_seeds() -> [Seed; 3] {
        [
            Seed([0, 1, 2, 3, 4, 5, 6, 7]),
            Seed([42, 42, 42, 42, 42, 42, 42, 42]),
            Seed([
                0x01234567, 0x89abcdef, 0xfedcba98, 0x76543210, 0x0f0f0f0f, 0xf0f0f0f0, 0x13579bdf,
                0x2468ace0,
            ]),
        ]
    }

    #[test]
    fn deterministic_parallel_matches_serial_baseline() {
        for seed in test_seeds() {
            for pow_bits in [17, 18, 20] {
                let (initial_state, base_input) = Blake2sTranscript::prepare_pow_search(&seed);
                let expected = Blake2sTranscript::search_pow_serial_from_prepared(
                    &seed,
                    pow_bits,
                    initial_state,
                    base_input,
                );
                for threads in [1, 2, 4] {
                    let worker = Worker::new_with_num_threads(threads);
                    let actual = Blake2sTranscript::search_pow(&seed, pow_bits, &worker);
                    assert_eq!(
                        actual, expected,
                        "seed={seed:?}, pow_bits={pow_bits}, threads={threads}"
                    );
                }
            }
        }
    }

    #[test]
    fn deterministic_parallel_result_is_invariant_across_worker_counts() {
        let seed = Seed([0xdeadbeef; 8]);
        let pow_bits = 19;
        let (initial_state, base_input) = Blake2sTranscript::prepare_pow_search(&seed);
        let expected = Blake2sTranscript::search_pow_serial_from_prepared(
            &seed,
            pow_bits,
            initial_state,
            base_input,
        );

        for threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(threads);
            let actual = Blake2sTranscript::search_pow(&seed, pow_bits, &worker);
            assert_eq!(actual, expected, "threads={threads}");
        }
    }
}
