use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceVariable;
use era_cudart::stream::CudaStream;
use serde::Deserialize;

use super::super::{keccak256_pow, transcript_commit_initial_u32, transcript_draw_fields, Seed};
use super::{download, upload};
use crate::upstream::{
    split_timestamp, GKRProof, Keccak256MerkleTreeWithCap, Keccak256Seed, Keccak256Transcript,
    MerkleTreeCapVarLength, OperationMode, Proth120, Transcript,
};

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;
type HostTranscript = Keccak256Transcript;

const LOOKUP_CHALLENGES_POW_BITS: u32 = 8;

#[derive(Deserialize)]
struct Bundle {
    proof: L1Proof,
    operation_mode: OperationMode,
}

fn l1_reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference_2p21")
        })
}

fn l1_bundle() -> Bundle {
    let path = l1_reference_dir().join("l1_bundle.json");
    let file = File::open(&path)
        .unwrap_or_else(|error| panic!("L1 reference open {}: {error}", path.display()));
    serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|error| panic!("L1 reference deserialize {}: {error}", path.display()))
}

fn cap_words(cap: &MerkleTreeCapVarLength) -> Vec<u32> {
    let mut words = Vec::new();
    cap.add_into_buffer(&mut words);
    words
}

struct Replay {
    stream: CudaStream,
    seed: DeviceAllocation<u8>,
    nonce: DeviceAllocation<u64>,
    counter: DeviceAllocation<u64>,
    host: Keccak256Seed,
}

impl Replay {
    fn new(host: Keccak256Seed) -> Self {
        let stream = CudaStream::default();
        let seed = upload(&host.0, &stream);
        let nonce = DeviceAllocation::alloc(1).unwrap();
        let counter = DeviceAllocation::alloc(1).unwrap();
        Self {
            stream,
            seed,
            nonce,
            counter,
            host,
        }
    }

    fn check(&self, step: &str) {
        let seed: Seed = download(&self.seed, 0, &self.stream).try_into().unwrap();
        assert_eq!(seed, self.host.0, "{step}: seed");
    }

    fn commit_initial(words: &[u32]) -> Self {
        let mut replay = Self::new(Keccak256Seed([0; 32]));
        let input = upload(words, &replay.stream);
        transcript_commit_initial_u32(&input, &mut replay.seed, &replay.stream).unwrap();
        replay.host = <HostTranscript as Transcript<Proth120, Proth120>>::commit_initial_u32(words);
        replay.check("commit_initial_u32");
        replay
    }

    fn draw_fields(&mut self, count: usize, step: &str) -> Vec<Proth120> {
        let mut out = upload(&vec![Proth120::new(0); count], &self.stream);
        transcript_draw_fields(&mut self.seed, &mut out, &self.stream).unwrap();
        let gpu = download(&out, Proth120::new(0), &self.stream);
        let mut expected = vec![Proth120::new(0); count];
        <HostTranscript as Transcript<Proth120, Proth120>>::draw_random_field_elements(
            &mut self.host,
            &mut expected,
        );
        assert_eq!(gpu, expected, "{step}: draws");
        self.check(step);
        gpu
    }

    fn pow(&mut self, bits: u32, expected: u64, step: &str) {
        let device_nonce = unsafe { DeviceVariable::from_raw_parts_mut(self.nonce.as_mut_ptr()) };
        let counter = unsafe { DeviceVariable::from_raw_parts_mut(self.counter.as_mut_ptr()) };
        keccak256_pow(&mut self.seed, bits, device_nonce, counter, &self.stream).unwrap();
        let mut nonce = [0u64];
        memory_copy_async(&mut nonce, &self.nonce, &self.stream).unwrap();
        self.stream.synchronize().unwrap();
        assert_eq!(nonce[0], expected, "{step}: nonce");
        <HostTranscript as Transcript<Proth120, Proth120>>::verify_pow(
            &mut self.host,
            expected,
            bits,
        );
        self.check(step);
    }
}

#[test]
#[ignore]
fn keccak256_l1_reference_replay() {
    let Bundle {
        proof,
        operation_mode,
    } = l1_bundle();
    let OperationMode::SingleChunk {
        external_challenges_pow_bits,
        register_final_state,
        final_pc,
        final_timestamp,
    } = operation_mode
    else {
        panic!("L1 reference bundle is not a single-chunk operation");
    };
    let whir = &proof.whir_proof;
    let schedule = &whir.whir_schedule;
    assert_eq!(schedule.base_round.lde_factor(), 128);
    assert_eq!(schedule.cap_size, 8);
    assert_eq!(schedule.fold_steps(), [1, 4, 4, 4, 4]);
    assert_eq!(schedule.queries_per_round(), [12, 11, 7, 6, 5]);
    assert_eq!(schedule.queries_pow_bits_per_round(), [30, 27, 30, 20, 17]);

    let mut words = Vec::new();
    for register in register_final_state.iter() {
        let (low, high) = split_timestamp(register.last_access_timestamp);
        words.extend([register.value, low, high]);
    }
    let (low, high) = split_timestamp(final_timestamp);
    words.extend([final_pc, low, high]);
    words.extend_from_slice(&proof.inits_and_teardowns_top_bits);
    words.extend(cap_words(&whir.setup_commitment.commitment.cap));
    words.extend(cap_words(&whir.memory_commitment.commitment.cap));
    let mut replay = Replay::commit_initial(&words);
    let lookup_bits = LOOKUP_CHALLENGES_POW_BITS.max(external_challenges_pow_bits);
    assert_eq!(lookup_bits, 20);
    replay.pow(lookup_bits, proof.lookup_challenges_pow_nonce, "lookup pow");
    let challenges = replay.draw_fields(9, "external challenges");
    let external = &proof.external_challenges;
    for (i, expected) in external
        .permutation_argument_linearization_challenges
        .iter()
        .enumerate()
    {
        assert_eq!(challenges[i], *expected, "linearization challenge {i}");
    }
    assert_eq!(
        challenges[external.permutation_argument_linearization_challenges.len()],
        external.permutation_argument_additive_part,
        "additive part"
    );

    // WHIR-phase Keccak transcript coverage is in gpu/whir/src/proth120/tests.rs and gpu/execution_prover/tests/l1_stage_parity.rs.
}
