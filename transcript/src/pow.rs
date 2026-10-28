use super::*;
use worker::Worker;

const BLAKE2S_NO_RESULT: u64 = u64::MAX;
const BLAKE2S_ROUNDS_PER_INVOCAITON: usize = 1 << 16u32;
/// Candidates checked between hit tests inside a chunk.
const POW_BATCH: u64 = 64;

impl<const REDUCED_ROUNDS: bool> Blake2sTranscript<REDUCED_ROUNDS> {
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
        let threshold = Self::pow_threshold(pow_bits);
        let mut input = base_input;
        for challenge in 0u64..(BLAKE2S_NO_RESULT - 1) {
            if Self::pow_challenge_matches(&mut input, &initial_state, challenge, threshold) {
                return Self::finalize_pow_result(seed, challenge, pow_bits);
            }
        }

        unreachable!("PoW search exhausted the nonce space without a result");
    }

    /// Parallel grind: nonce chunks of `BLAKE2S_ROUNDS_PER_INVOCAITON` are
    /// handed out DYNAMICALLY (an atomic counter), so a slow thread (an
    /// efficiency core, a preempted core) just takes fewer chunks instead of
    /// gating the whole search with its share of a static stripe. (A
    /// four-wide check — four scalar chains in lockstep or the four-lane NEON
    /// compression — measured SLOWER per candidate than the plain single
    /// check on Apple M3: 27 vs 23 ns; the single check already keeps the
    /// core busy.)
    ///
    /// `deterministic_pow`: the result is the SMALLEST valid nonce, identical
    /// to the serial search — a worker gives up only when the next chunk
    /// starts at or past the best nonce found so far (the best only
    /// decreases, so a skipped chunk can never contain a smaller one), and a
    /// chunk is scanned in increasing order so its first hit is its minimum.
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
        let next_chunk = std::sync::Arc::new(AtomicU64::new(0));
        let threshold = Self::pow_threshold(pow_bits);
        let chunk_len = BLAKE2S_ROUNDS_PER_INVOCAITON as u64;
        let num_workers = worker.num_cores as u64;
        let last_nonce = BLAKE2S_NO_RESULT - 1;

        worker.scope(usize::MAX, |scope, _| {
            for worker_idx in 0..num_workers {
                let result = std::sync::Arc::clone(&result);
                let next_chunk = std::sync::Arc::clone(&next_chunk);
                Worker::smart_spawn(scope, worker_idx == num_workers - 1, move |_| {
                    let mut input = base_input;
                    loop {
                        let chunk = next_chunk.fetch_add(1, Ordering::Relaxed);
                        let Some(base) = chunk.checked_mul(chunk_len) else {
                            break;
                        };
                        if base >= last_nonce {
                            break;
                        }
                        #[cfg(feature = "deterministic_pow")]
                        if result.load(Ordering::Relaxed) <= base {
                            break;
                        }
                        #[cfg(not(feature = "deterministic_pow"))]
                        if result.load(Ordering::Relaxed) != BLAKE2S_NO_RESULT {
                            break;
                        }
                        let end = (base + chunk_len).min(last_nonce);
                        let mut found = None;
                        // batches without an early exit: consecutive
                        // candidates are independent, and a plain loop lets
                        // the core overlap their compressions (measured 2x
                        // the throughput of a check-and-break loop); a batch
                        // with a hit is rescanned for its first one
                        let mut c = base;
                        'chunk: while c < end {
                            let batch_end = (c + POW_BATCH).min(end);
                            let mut any = false;
                            for cc in c..batch_end {
                                any |= Self::pow_challenge_matches(
                                    &mut input,
                                    &initial_state,
                                    cc,
                                    threshold,
                                );
                            }
                            if any {
                                for cc in c..batch_end {
                                    if Self::pow_challenge_matches(
                                        &mut input,
                                        &initial_state,
                                        cc,
                                        threshold,
                                    ) {
                                        found = Some(cc);
                                        break 'chunk;
                                    }
                                }
                            }
                            c = batch_end;
                        }
                        if let Some(nonce) = found {
                            #[cfg(feature = "deterministic_pow")]
                            result.fetch_min(nonce, Ordering::Relaxed);
                            #[cfg(not(feature = "deterministic_pow"))]
                            let _ = result.compare_exchange(
                                BLAKE2S_NO_RESULT,
                                nonce,
                                Ordering::Relaxed,
                                Ordering::Relaxed,
                            );
                            // every later chunk starts past this nonce
                            return;
                        }
                    }
                })
            }
        });

        let challenge_u64 = result.load(Ordering::Relaxed);
        assert!(
            challenge_u64 != BLAKE2S_NO_RESULT,
            "PoW search exhausted the nonce space without a result"
        );
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
        if REDUCED_ROUNDS {
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

    type T = Blake2sTranscript;

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

    /// Per-candidate cost of the check and grind timings, one and eight
    /// threads (`#[ignore]`d bench).
    #[test]
    #[ignore]
    fn pow_check_bench() {
        let seed = Seed([7, 7, 7, 7, 7, 7, 7, 7]);
        let (initial_state, base_input) = T::prepare_pow_search(&seed);
        const N: u64 = 1 << 20;
        let mut input = base_input;
        let t = std::time::Instant::now();
        let mut hits = 0u32;
        for c in 0..N {
            hits += T::pow_challenge_matches(&mut input, &initial_state, c, 0) as u32;
        }
        let d1 = t.elapsed();
        println!(
            "[pow-bench] single {:.1} ns/candidate (hits {hits})",
            d1.as_secs_f64() * 1e9 / N as f64
        );
        for threads in [1usize, 8] {
            let worker = Worker::new_with_num_threads(threads);
            let t = std::time::Instant::now();
            let (_, nonce) = T::search_pow(&seed, 24, &worker);
            println!(
                "[pow-bench] 24-bit grind, {threads} thr: {:.3?} (nonce {nonce})",
                t.elapsed()
            );
        }
    }

    #[test]
    fn deterministic_parallel_matches_serial_baseline() {
        for seed in test_seeds() {
            for pow_bits in [17, 18, 20] {
                let (initial_state, base_input) = T::prepare_pow_search(&seed);
                let expected =
                    T::search_pow_serial_from_prepared(&seed, pow_bits, initial_state, base_input);
                for threads in [1, 2, 4] {
                    let worker = Worker::new_with_num_threads(threads);
                    let actual = T::search_pow(&seed, pow_bits, &worker);
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
        let (initial_state, base_input) = T::prepare_pow_search(&seed);
        let expected =
            T::search_pow_serial_from_prepared(&seed, pow_bits, initial_state, base_input);

        for threads in [1, 2, 4, 8] {
            let worker = Worker::new_with_num_threads(threads);
            let actual = T::search_pow(&seed, pow_bits, &worker);
            assert_eq!(actual, expected, "threads={threads}");
        }
    }
}
