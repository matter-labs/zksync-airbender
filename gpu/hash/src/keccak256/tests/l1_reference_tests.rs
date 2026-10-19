use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::time::Instant;

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceVariable;
use era_cudart::stream::CudaStream;
use serde::Deserialize;

use super::super::{
    keccak256_pow, transcript_commit_fields, transcript_commit_initial_u32, transcript_commit_u32,
    transcript_draw_fields, transcript_draw_u32, Seed,
};
use super::{bitreverse_index, download, upload};
use crate::upstream::{
    assemble_query_index, split_timestamp, BitSource, CommitmentMode, GKRProof,
    Keccak256MerkleTreeWithCap, Keccak256Seed, Keccak256Transcript, MerkleTreeCapVarLength,
    Proth120, Transcript,
};

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;
type HostTranscript = Keccak256Transcript;

const LOOKUP_CHALLENGES_POW_BITS: u32 = 8;
const BASE_LOG_DOMAIN: u32 = 24;
const BASE_LOG_VALUES_PER_LEAF: u32 = 1;

#[derive(Deserialize)]
struct Bundle {
    proof: L1Proof,
    commitment_mode: CommitmentMode,
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

    fn commit_u32(&mut self, words: &[u32], step: &str) {
        let input = upload(words, &self.stream);
        transcript_commit_u32(&mut self.seed, &input, &self.stream).unwrap();
        <HostTranscript as Transcript<Proth120, Proth120>>::commit_u32_with_seed(
            &mut self.host,
            words,
        );
        self.check(step);
    }

    fn commit_fields(&mut self, fields: &[Proth120], step: &str) {
        let input = upload(fields, &self.stream);
        transcript_commit_fields(&mut self.seed, &input, &self.stream).unwrap();
        <HostTranscript as Transcript<Proth120, Proth120>>::commit_base_field_elements(
            &mut self.host,
            fields,
        );
        self.check(step);
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

    fn draw_u32(&mut self, count: usize, step: &str) -> Vec<u32> {
        let mut out = upload(&vec![0u32; count], &self.stream);
        transcript_draw_u32(&mut self.seed, &mut out, &self.stream).unwrap();
        let gpu = download(&out, 0, &self.stream);
        let mut expected = vec![0u32; count];
        <HostTranscript as Transcript<Proth120, Proth120>>::draw_randomness(
            &mut self.host,
            &mut expected,
        );
        assert_eq!(gpu, expected, "{step}: words");
        self.check(step);
        gpu
    }

    fn pow(&mut self, bits: u32, expected: u64, step: &str) -> f64 {
        let start = Instant::now();
        let device_nonce = unsafe { DeviceVariable::from_raw_parts_mut(self.nonce.as_mut_ptr()) };
        let counter = unsafe { DeviceVariable::from_raw_parts_mut(self.counter.as_mut_ptr()) };
        keccak256_pow(&mut self.seed, bits, device_nonce, counter, &self.stream).unwrap();
        let mut nonce = [0u64];
        memory_copy_async(&mut nonce, &self.nonce, &self.stream).unwrap();
        self.stream.synchronize().unwrap();
        let elapsed = start.elapsed().as_secs_f64();
        assert_eq!(nonce[0], expected, "{step}: nonce");
        <HostTranscript as Transcript<Proth120, Proth120>>::verify_pow(
            &mut self.host,
            expected,
            bits,
        );
        self.check(step);
        elapsed
    }
}

fn query_tree_indexes(words: &[u32], count: usize, log_leaves: u32, log_lde: u32) -> Vec<usize> {
    let bits = (log_leaves + log_lde) as usize;
    let mut source = BitSource::new(words[1..].to_vec());
    (0..count)
        .map(|_| {
            let query = assemble_query_index(bits, &mut source);
            let coset = query & ((1 << log_lde) - 1);
            (bitreverse_index(coset, log_lde) << log_leaves) + (query >> log_lde)
        })
        .collect()
}

#[test]
#[ignore]
fn keccak256_l1_reference_replay() {
    let started = Instant::now();
    let Bundle {
        proof,
        commitment_mode,
    } = l1_bundle();
    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        pack_log2,
        external_challenges_pow_bits,
        register_final_state,
        final_pc,
        final_timestamp,
    } = commitment_mode
    else {
        panic!("L1 reference bundle is not in the packed commitment mode");
    };
    assert_eq!(pack_log2, 3);
    let whir = &proof.whir_proof;
    let schedule = &whir.whir_schedule;
    assert_eq!(schedule.base_lde_factor, 128);
    assert_eq!(schedule.cap_size, 8);
    assert_eq!(schedule.whir_steps_schedule, [1, 4, 4, 4, 4]);
    assert_eq!(schedule.whir_queries_schedule, [12, 11, 7, 6, 5]);
    assert_eq!(schedule.whir_pow_schedule, [30, 27, 30, 20, 17]);
    let mut nonces = Vec::new();

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
    let seconds = replay.pow(lookup_bits, proof.lookup_challenges_pow_nonce, "lookup pow");
    nonces.push((lookup_bits, proof.lookup_challenges_pow_nonce, seconds));
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

    let mut replay = Replay::new(Keccak256Seed(
        proof
            .intermediate_transcript_seed
            .expect("L1 reference has an intermediate transcript seed"),
    ));
    let mut polys = whir.sumcheck_polys.iter();
    let rounds = schedule.whir_steps_schedule.len();
    let mut checked_queries = 0;
    for round in 0..rounds {
        for step in 0..schedule.whir_steps_schedule[round] {
            let poly = polys.next().expect("sumcheck polynomial");
            replay.commit_fields(poly, &format!("round {round} sumcheck {step}"));
            replay.draw_fields(1, &format!("round {round} folding {step}"));
        }
        if round + 1 < rounds {
            replay.commit_u32(
                &cap_words(&whir.intermediate_whir_oracles[round].commitment.cap),
                &format!("round {round} cap"),
            );
            replay.draw_fields(1, &format!("round {round} ood point"));
            replay.commit_fields(
                &[whir.ood_samples[round]],
                &format!("round {round} ood value"),
            );
        } else {
            assert_eq!(whir.final_monomials.len(), 128);
            replay.commit_fields(&whir.final_monomials, "final monomials");
        }
        let bits = schedule.whir_pow_schedule[round];
        let seconds = replay.pow(bits, whir.pow_nonces[round], &format!("round {round} pow"));
        nonces.push((bits, whir.pow_nonces[round], seconds));
        let (log_leaves, log_lde, expected): (u32, u32, Vec<usize>) = if round == 0 {
            let expected: Vec<usize> = whir
                .memory_commitment
                .queries
                .iter()
                .map(|q| q.index)
                .collect();
            let setup: Vec<usize> = whir
                .setup_commitment
                .queries
                .iter()
                .map(|q| q.index)
                .collect();
            assert_eq!(setup, expected);
            (
                BASE_LOG_DOMAIN - BASE_LOG_VALUES_PER_LEAF,
                schedule.base_lde_factor.trailing_zeros(),
                expected,
            )
        } else {
            let expected = whir.intermediate_whir_oracles[round - 1]
                .queries
                .iter()
                .map(|q| q.index)
                .collect();
            (
                BASE_LOG_DOMAIN
                    - schedule.whir_steps_schedule[..round].iter().sum::<usize>() as u32
                    - schedule.whir_steps_schedule[round] as u32,
                schedule.whir_steps_lde_factors[round - 1].trailing_zeros(),
                expected,
            )
        };
        let count = schedule.whir_queries_schedule[round];
        assert_eq!(expected.len(), count);
        let query_bits = (log_leaves + log_lde) as usize;
        let words = (count * query_bits).div_ceil(32) + 1;
        let drawn = replay.draw_u32(
            words.next_multiple_of(8),
            &format!("round {round} query words"),
        );
        let indexes = query_tree_indexes(&drawn, count, log_leaves, log_lde);
        assert_eq!(indexes, expected, "round {round} query indexes");
        checked_queries += count;
        if round + 1 < rounds {
            replay.draw_fields(1, &format!("round {round} delinearization"));
        }
    }
    assert!(polys.next().is_none());
    assert_eq!(checked_queries, 41);
    assert_eq!(nonces.len(), 6);
    for (bits, nonce, seconds) in &nonces {
        println!(
            "keccak256_l1_reference_replay pow bits={bits} nonce={nonce} seconds={seconds:.3}"
        );
    }
    println!(
        "keccak256_l1_reference_replay wall seconds={:.3}",
        started.elapsed().as_secs_f64()
    );
}
