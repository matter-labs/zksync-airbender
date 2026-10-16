use std::mem::ManuallyDrop;
use std::panic::{catch_unwind, AssertUnwindSafe};

use era_cudart::memory::DeviceAllocation;
#[cfg(feature = "deterministic_pow")]
use era_cudart::slice::DeviceSlice;
use era_cudart::slice::DeviceVariable;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaError;
use sha3::{Digest as _, Keccak256};

#[cfg(feature = "deterministic_pow")]
use super::super::transcript::pow_chunk_steps;
use super::super::transcript::{pow_finalize, pow_search_bounded};
use super::super::{keccak256_pow, pow_helpers_probe, Seed};
#[cfg(feature = "deterministic_pow")]
use super::super::{transcript_draw_fields, transcript_draw_u32};
use super::{download, test_worker, upload, TestRng};
#[cfg(feature = "deterministic_pow")]
use crate::upstream::{assemble_query_index, BitSource};
use crate::upstream::{Keccak256Seed, Keccak256Transcript, Proth120, Transcript};

type HostTranscript = Keccak256Transcript;
const GUARD: u8 = 0x5c;

struct PowState {
    seed: DeviceAllocation<u8>,
    nonce: DeviceAllocation<u64>,
    counter: DeviceAllocation<u64>,
    offset: usize,
}

impl PowState {
    fn new(seed: &Seed, offset: usize, stream: &CudaStream) -> Self {
        let mut bytes = vec![GUARD; offset + 32 + 7];
        bytes[offset..offset + 32].copy_from_slice(seed);
        Self {
            seed: upload(&bytes, stream),
            nonce: upload(&[0x5eed_5eed_5eed_5eed], stream),
            counter: upload(&[0x5eed_5eed_5eed_5eed], stream),
            offset,
        }
    }

    #[cfg(feature = "deterministic_pow")]
    fn seed_slice(&mut self) -> &mut DeviceSlice<u8> {
        &mut self.seed[self.offset..self.offset + 32]
    }

    fn run(&mut self, bits: u32, stream: &CudaStream) {
        let nonce = unsafe { DeviceVariable::from_raw_parts_mut(self.nonce.as_mut_ptr()) };
        let counter = unsafe { DeviceVariable::from_raw_parts_mut(self.counter.as_mut_ptr()) };
        keccak256_pow(
            &mut self.seed[self.offset..self.offset + 32],
            bits,
            nonce,
            counter,
            stream,
        )
        .unwrap();
    }

    fn search(&mut self, bits: u32, bound: u64, blocks: u32, stream: &CudaStream) {
        self.search_from(bits, bound, blocks, 0, stream);
    }

    fn search_from(
        &mut self,
        bits: u32,
        bound: u64,
        blocks: u32,
        first_chunk: u64,
        stream: &CudaStream,
    ) {
        let nonce = unsafe { DeviceVariable::from_raw_parts_mut(self.nonce.as_mut_ptr()) };
        let counter = unsafe { DeviceVariable::from_raw_parts_mut(self.counter.as_mut_ptr()) };
        pow_search_bounded(
            &self.seed[self.offset..self.offset + 32],
            bits,
            bound,
            blocks,
            first_chunk,
            nonce,
            counter,
            stream,
        )
        .unwrap();
    }

    fn finalize(&mut self, bits: u32, stream: &CudaStream) {
        let nonce = unsafe { DeviceVariable::from_raw_parts(self.nonce.as_ptr()) };
        pow_finalize(
            &mut self.seed[self.offset..self.offset + 32],
            bits,
            nonce,
            stream,
        )
        .unwrap();
    }

    fn read_seed(&self, stream: &CudaStream) -> Seed {
        let bytes = download(&self.seed, 0, stream);
        assert!(bytes[..self.offset].iter().all(|byte| *byte == GUARD));
        assert!(bytes[self.offset + 32..].iter().all(|byte| *byte == GUARD));
        bytes[self.offset..self.offset + 32].try_into().unwrap()
    }

    fn read_nonce(&self, stream: &CudaStream) -> u64 {
        download(&self.nonce, 0, stream)[0]
    }

    #[cfg(feature = "deterministic_pow")]
    fn read_counter(&self, stream: &CudaStream) -> u64 {
        download(&self.counter, 0, stream)[0]
    }
}

fn cpu_digest(seed: &Seed, nonce: u64) -> Seed {
    let mut hash = Keccak256::new();
    hash.update(seed);
    hash.update(nonce.to_be_bytes());
    hash.finalize().into()
}

fn cpu_predicate(digest: &Seed, bits: u32) -> bool {
    assert!(bits <= 256);
    let bytes = (bits / 8) as usize;
    let partial = bits % 8;
    digest[..bytes].iter().all(|byte| *byte == 0)
        && (partial == 0 || digest[bytes] >> (8 - partial) == 0)
}

fn sequential_minimum(seed: &Seed, bits: u32) -> u64 {
    (0..u64::MAX)
        .find(|nonce| cpu_predicate(&cpu_digest(seed, *nonce), bits))
        .unwrap()
}

fn assert_named_panic(name: &str, condition: &str, action: impl FnOnce()) {
    let error = catch_unwind(AssertUnwindSafe(action)).expect_err("expected named panic");
    let message = error
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| error.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(
        message.contains(&format!("keccak256::{name}: {condition}")),
        "{message}"
    );
}

#[cfg(feature = "deterministic_pow")]
#[test]
fn keccak256_pow_min_nonce_parity() {
    let stream = CudaStream::default();
    let worker = test_worker();
    let mut rng = TestRng::new(0x706f_776d_696e);
    let seeds = [
        [0u8; 32],
        std::array::from_fn(|index| index as u8),
        std::array::from_fn(|_| rng.next_u64() as u8),
    ];
    for (index, seed) in seeds.iter().enumerate() {
        for bits in [0u32, 1, 4, 8, 11, 12, 16, 20] {
            let (expected, minimum) =
                <HostTranscript as Transcript<Proth120, Proth120>>::search_pow(
                    &Keccak256Seed(*seed),
                    bits,
                    &worker,
                );
            if bits <= 16 {
                assert_eq!(minimum, sequential_minimum(seed, bits));
            }
            assert_eq!(expected.0, cpu_digest(seed, minimum));
            let mut verified = Keccak256Seed(*seed);
            <HostTranscript as Transcript<Proth120, Proth120>>::verify_pow(
                &mut verified,
                minimum,
                bits,
            );
            assert_eq!(verified, expected);
            let offset = [0, 1, 7][index];
            let mut public = PowState::new(seed, offset, &stream);
            public.run(bits, &stream);
            assert_eq!(
                public.read_nonce(&stream),
                minimum,
                "seed={index} bits={bits}"
            );
            assert_eq!(
                public.read_seed(&stream),
                expected.0,
                "seed={index} bits={bits}"
            );
            let bound = minimum.checked_add(1).unwrap().max(17 * 128);
            for blocks in [1, 2, 17] {
                let mut bounded = PowState::new(seed, offset, &stream);
                bounded.search(bits, bound, blocks, &stream);
                assert_eq!(
                    bounded.read_nonce(&stream),
                    minimum,
                    "seed={index} bits={bits} blocks={blocks}"
                );
                assert_eq!(
                    bounded.read_seed(&stream),
                    *seed,
                    "search must not update seed"
                );
                bounded.finalize(bits, &stream);
                assert_eq!(
                    bounded.read_seed(&stream),
                    expected.0,
                    "seed={index} bits={bits} blocks={blocks}"
                );
            }
            println!("pow seed={index} bits={bits} minimum={minimum} grids=1,2,17");
        }
    }
    let (seed, hits) = (0u16..256)
        .find_map(|candidate| {
            let mut seed = [0u8; 32];
            seed[..2].copy_from_slice(&candidate.to_le_bytes());
            let hits: Vec<_> = (0..128u64)
                .filter(|nonce| cpu_predicate(&cpu_digest(&seed, *nonce), 4))
                .take(2)
                .collect();
            (hits.len() == 2).then_some((seed, hits))
        })
        .unwrap();
    assert!(hits[0] < hits[1]);
    for blocks in [1, 2, 17] {
        let mut state = PowState::new(&seed, 1, &stream);
        state.search(4, 17 * 128, blocks, &stream);
        assert_eq!(
            state.read_nonce(&stream),
            hits[0],
            "lower stripe must win over another hit"
        );
    }
    println!(
        "multi-hit lower_stripe={} higher_stripe={}",
        hits[0], hits[1]
    );
}

#[test]
fn keccak256_pow_boundaries() {
    let stream = CudaStream::default();
    let mut digests = Vec::new();
    let mut bit_counts = Vec::new();
    let mut candidates = Vec::new();
    let mut strides = Vec::new();
    for bits in [0u32, 1, 7, 8, 31, 32, 33, 64, 65, 255, 256] {
        for index in 0..258 {
            let mut digest = [0u8; 32];
            if index == 1 {
                digest.fill(0xff);
            }
            if index >= 2 {
                let bit = index - 2;
                digest[bit / 8] = 1 << (7 - bit % 8);
            }
            digests.extend_from_slice(&digest);
            bit_counts.push(bits);
            candidates.push(u64::MAX - 128);
            strides.push(128u64);
        }
    }
    for stride in [0u64, 1, 2, 127, 128, 2176, u64::MAX - 1, u64::MAX] {
        let boundary = u64::MAX - stride;
        let mut values = vec![0, 1, u64::MAX - 1, u64::MAX, boundary];
        if boundary > 0 {
            values.push(boundary - 1);
        }
        if boundary < u64::MAX {
            values.push(boundary + 1);
        }
        for candidate in values {
            digests.extend_from_slice(&[0u8; 32]);
            bit_counts.push(0);
            candidates.push(candidate);
            strides.push(stride);
        }
    }
    let count = bit_counts.len();
    let input = upload(&digests, &stream);
    let bits = upload(&bit_counts, &stream);
    let nonces = upload(&candidates, &stream);
    let steps = upload(&strides, &stream);
    let mut predicates = upload(&vec![0xaaaa_aaaau32; count + 2], &stream);
    let mut next = upload(&vec![0xaaaa_aaaa_aaaa_aaaau64; count + 2], &stream);
    let mut can = upload(&vec![0xaaaa_aaaau32; count + 2], &stream);
    pow_helpers_probe(
        &input,
        &bits,
        &nonces,
        &steps,
        &mut predicates[..count],
        &mut next[..count],
        &mut can[..count],
        &stream,
    )
    .unwrap();
    let predicates = download(&predicates, 0, &stream);
    let next = download(&next, 0, &stream);
    let can = download(&can, 0, &stream);
    for index in 0..count {
        let digest: Seed = digests[index * 32..(index + 1) * 32].try_into().unwrap();
        assert_eq!(
            predicates[index],
            u32::from(cpu_predicate(&digest, bit_counts[index])),
            "predicate index={index}"
        );
        let expected = candidates[index]
            .checked_add(strides[index])
            .filter(|next| *next < u64::MAX);
        assert_eq!(
            can[index],
            u32::from(expected.is_some()),
            "advance index={index}"
        );
        assert_eq!(next[index], expected.unwrap_or(0), "advance index={index}");
    }
    assert_eq!(&predicates[count..], &[0xaaaa_aaaa; 2]);
    assert_eq!(&next[count..], &[0xaaaa_aaaa_aaaa_aaaa; 2]);
    assert_eq!(&can[count..], &[0xaaaa_aaaa; 2]);
    let seed = [0x5au8; 32];
    let mut state = PowState::new(&seed, 1, &stream);
    assert_named_panic("keccak256_pow", "bits <= 256", || state.run(257, &stream));
    assert_named_panic("pow_search_bounded", "blocks > 0", || {
        state.search(1, 128, 0, &stream)
    });
    assert_named_panic("pow_search_bounded", "stride <= max_nonce", || {
        state.search(1, 127, 1, &stream)
    });
    assert_eq!(state.read_seed(&stream), seed);
    assert_eq!(state.read_nonce(&stream), 0x5eed_5eed_5eed_5eed);
    let (endpoint_seed, minimum) = (0u16..256)
        .find_map(|candidate| {
            let mut seed = [0u8; 32];
            seed[..2].copy_from_slice(&candidate.to_le_bytes());
            let minimum = sequential_minimum(&seed, 8);
            (minimum >= 128).then_some((seed, minimum))
        })
        .unwrap();
    let mut endpoint = PowState::new(&endpoint_seed, 7, &stream);
    endpoint.search(8, minimum + 1, 1, &stream);
    assert_eq!(endpoint.read_nonce(&stream), minimum);
    endpoint.finalize(8, &stream);
    assert_eq!(
        endpoint.read_seed(&stream),
        cpu_digest(&endpoint_seed, minimum)
    );
    let mut excluded = PowState::new(&endpoint_seed, 0, &stream);
    excluded.search(8, minimum, 1, &stream);
    assert_eq!(
        excluded.read_nonce(&stream),
        u64::MAX,
        "exclusive endpoint keeps the no-hit sentinel"
    );
    assert_eq!(excluded.read_seed(&stream), endpoint_seed);
    let mut sentinel = PowState::new(&seed, 1, &stream);
    sentinel.nonce = upload(&[u64::MAX], &stream);
    sentinel.finalize(0, &stream);
    assert_eq!(sentinel.read_nonce(&stream), u64::MAX);
    assert_eq!(sentinel.read_seed(&stream), cpu_digest(&seed, u64::MAX));
    println!(
        "boundaries probe_count={count} endpoint_minimum={minimum} sentinel_nonce={}",
        u64::MAX
    );
}

#[cfg(feature = "deterministic_pow")]
#[test]
fn keccak256_pow_draw_sequence_parity() {
    let stream = CudaStream::default();
    let worker = test_worker();
    let seed: Seed = std::array::from_fn(|index| (index * 7 + 3) as u8);
    for count in [0usize, 1, 9] {
        let mut state = PowState::new(&seed, 1, &stream);
        state.run(11, &stream);
        let mut out = upload(&vec![Proth120::new(7); count + 1], &stream);
        transcript_draw_fields(state.seed_slice(), &mut out[..count], &stream).unwrap();
        let gpu = download(&out, Proth120::new(0), &stream);
        let mut expected = vec![Proth120::new(0); count];
        let (expected_seed, expected_nonce) =
            <HostTranscript as Transcript<Proth120, Proth120>>::draw_random_field_elements_with_pow(
                &Keccak256Seed(seed),
                11,
                &mut expected,
                &worker,
            );
        assert_eq!(&gpu[..count], &expected);
        assert_eq!(gpu[count], Proth120::new(7));
        assert_eq!(state.read_nonce(&stream), expected_nonce);
        assert_eq!(state.read_seed(&stream), expected_seed.0);
    }
    let mut state = PowState::new(&seed, 7, &stream);
    state.run(11, &stream);
    let mut out = upload(&[0xdead_beefu32; 26], &stream);
    transcript_draw_u32(state.seed_slice(), &mut out[..24], &stream).unwrap();
    let words = download(&out, 0, &stream);
    assert_eq!(&words[24..], &[0xdead_beef; 2]);
    let mut host_seed = Keccak256Seed(seed);
    let (expected_nonce, mut host_bits) = prover::gkr::prover::transcript_utils::draw_query_bits::<
        Proth120,
        Proth120,
        HostTranscript,
    >(&mut host_seed, 17 * 29, 11, &worker);
    assert_eq!(
        (17usize * 29)
            .div_ceil(32)
            .checked_add(1)
            .unwrap()
            .next_multiple_of(8),
        24
    );
    assert_eq!(state.read_nonce(&stream), expected_nonce);
    assert_eq!(state.read_seed(&stream), host_seed.0);
    let mut gpu_bits = BitSource::new(words[1..24].to_vec());
    let mut unskipped_bits = BitSource::new(words[..24].to_vec());
    let mut expected_queries = Vec::new();
    let mut unskipped_queries = Vec::new();
    for _ in 0..17 {
        let expected = assemble_query_index(29, &mut host_bits);
        assert_eq!(assemble_query_index(29, &mut gpu_bits), expected);
        expected_queries.push(expected);
        unskipped_queries.push(assemble_query_index(29, &mut unskipped_bits));
    }
    assert_ne!(
        unskipped_queries, expected_queries,
        "word zero must be skipped"
    );
}

#[cfg(not(feature = "deterministic_pow"))]
#[test]
fn keccak256_pow_first_hit_is_valid() {
    let stream = CudaStream::default();
    let worker = test_worker();
    let mut rng = TestRng::new(0x706f_7766_6972);
    let seeds = [
        [0u8; 32],
        std::array::from_fn(|index| index as u8),
        std::array::from_fn(|_| rng.next_u64() as u8),
    ];
    for (index, seed) in seeds.iter().enumerate() {
        for bits in [0u32, 1, 4, 8, 11, 12, 16, 20] {
            let offset = [0, 1, 7][index];
            let mut public = PowState::new(seed, offset, &stream);
            public.run(bits, &stream);
            let nonce = public.read_nonce(&stream);
            let digest = cpu_digest(seed, nonce);
            assert!(cpu_predicate(&digest, bits), "seed={index} bits={bits}");
            assert_eq!(
                public.read_seed(&stream),
                digest,
                "seed={index} bits={bits}"
            );
            let (_, minimum) = <HostTranscript as Transcript<Proth120, Proth120>>::search_pow(
                &Keccak256Seed(*seed),
                bits,
                &worker,
            );
            let bound = minimum.checked_add(1).unwrap().max(17 * 128);
            for blocks in [1, 2, 17] {
                let mut bounded = PowState::new(seed, offset, &stream);
                bounded.search(bits, bound, blocks, &stream);
                let nonce = bounded.read_nonce(&stream);
                assert!(nonce < bound, "seed={index} bits={bits} blocks={blocks}");
                assert!(
                    cpu_predicate(&cpu_digest(seed, nonce), bits),
                    "seed={index} bits={bits} blocks={blocks}"
                );
            }
            println!("pow seed={index} bits={bits} first_hit={nonce} minimum={minimum}");
        }
    }
}

#[cfg(feature = "deterministic_pow")]
#[test]
fn keccak256_pow_counter_reaches_top_of_nonce_domain() {
    let stream = CudaStream::default();
    let seed = [0x3cu8; 32];
    let bits = 4;
    for blocks in [1, 2, 17] {
        assert_eq!(pow_chunk_steps(bits, blocks), 1);
    }
    let first_chunk = u64::MAX / 32 - 4;
    let hits: Vec<u64> = (first_chunk * 32..u64::MAX)
        .filter(|nonce| cpu_predicate(&cpu_digest(&seed, *nonce), bits))
        .collect();
    assert!(!hits.is_empty());
    for blocks in [1, 2, 17] {
        let mut state = PowState::new(&seed, 0, &stream);
        state.search_from(bits, u64::MAX, blocks, first_chunk, &stream);
        let nonce = state.read_nonce(&stream);
        if cfg!(feature = "deterministic_pow") {
            assert_eq!(nonce, hits[0], "blocks={blocks}");
        } else {
            assert!(hits.contains(&nonce), "blocks={blocks}");
        }
    }
    let chunk = 32 * pow_chunk_steps(256, 1) as u64;
    let last_chunk = (u64::MAX - 1) / chunk;
    let mut state = PowState::new(&seed, 0, &stream);
    state.search_from(256, u64::MAX, 1, last_chunk, &stream);
    assert_eq!(state.read_nonce(&stream), u64::MAX);
    assert_eq!(state.read_counter(&stream), last_chunk + 5);
    let mut state = PowState::new(&seed, 0, &stream);
    state.search_from(256, u64::MAX, 1, u64::MAX / 32, &stream);
    assert_eq!(state.read_nonce(&stream), u64::MAX);
    assert_eq!(state.read_counter(&stream), u64::MAX / 32 + 4);
    println!("top-of-domain hits={} first={}", hits.len(), hits[0]);
}

#[test]
#[ignore]
fn keccak256_pow_exhaustion() {
    let seed = [0x5au8; 32];
    let bound = 128u64;
    assert!((0..=bound).all(|nonce| !cpu_predicate(&cpu_digest(&seed, nonce), 256)));
    let stream = ManuallyDrop::new(CudaStream::default());
    let mut state = ManuallyDrop::new(PowState::new(&seed, 1, &stream));
    state.search(256, bound, 1, &stream);
    assert_eq!(state.read_nonce(&stream), u64::MAX);
    assert_eq!(state.read_seed(&stream), seed);
    state.finalize(256, &stream);
    let error = stream
        .synchronize()
        .expect_err("expected deliberate exhaustion trap");
    assert_eq!(error, CudaError::ErrorLaunchFailure);
    println!("observed expected CUDA trap: {error:?}");
}
