use era_cudart::memory::DeviceAllocation;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use sha3::{Digest as _, Keccak256};

use super::super::transcript::{pow_finalize, pow_search_bounded};
use super::super::{keccak256_pow, transcript_draw_fields, transcript_draw_u32, Seed};
use super::{download, test_worker, upload, TestRng};
use crate::upstream::{
    assemble_query_index, BitSource, Keccak256Seed, Keccak256Transcript, Proth120, Transcript,
};

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
    {
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
            let (expected_seed, expected_nonce) = <HostTranscript as Transcript<
                Proth120,
                Proth120,
            >>::draw_random_field_elements_with_pow(
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
        let (expected_nonce, mut host_bits) =
            prover::gkr::prover::transcript_utils::draw_query_bits::<
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
}
