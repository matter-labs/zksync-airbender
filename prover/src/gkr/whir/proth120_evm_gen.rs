//! Generates WHIR proof input data over `Proth120` with a Keccak256 transcript
//! and Keccak256 Merkle trees, matching the byte layout expected by the EVM
//! (Solidity) WHIR verifier, and dumps it to JSON for cross-checking.
//!
//! This runs a deliberately small "test" schedule (message 2^8, initial LDE 32
//! => RS codeword 2^13, 8 witness + 1 setup columns, folds all 1, no PoW) so it
//! executes locally in seconds. The production target is message 2^26 with the
//! 100-bit-security schedule; only the sizes differ, not the logic.

use super::*;
use crate::gkr::prover::stages::stage1::commit_trace_part;
use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use field::Proth120;
use rand::{Rng, SeedableRng};
use std::alloc::Global;
use transcript::{Keccak256Seed, Keccak256Transcript};

type Tree = Keccak256MerkleTreeWithCap<Global>;

const N: usize = 8; // message log size (2^8 elements per column)
const LDE_LOG2: usize = 5; // initial LDE factor 32 = 2^5
const CAP_SIZE: usize = 8; // matches EVM CAP (CAP_LOG2 = 3)
const FIRST_FOLD_LOG2: usize = 1; // round-0 fold => values_per_leaf = 2

fn rand_proth<R: Rng>(rng: &mut R) -> Proth120 {
    let lo: u64 = rng.random();
    let hi: u64 = rng.random();
    Proth120::new((((hi as u128) << 64) | lo as u128) % Proth120::ORDER)
}

#[test]
fn generate_whir_input_for_evm() {
    let worker = Worker::new_with_num_threads(1);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xC0FFEE);

    let trace_len = 1usize << N; // 256
    let lde_factor = 1usize << LDE_LOG2; // 32
    let codeword = trace_len * lde_factor; // 2^13 (RS codeword size)
    // Twiddles are for the message-size NTT used per LDE coset (matches the
    // production prove path, which builds `Twiddles::new(trace_len)`).
    let twiddles = fft::Twiddles::<Proth120, Global>::new(trace_len, &worker);

    // --- 8 witness + 1 setup random polynomials (values on the boolean hypercube) ---
    let witness: Vec<Vec<Proth120>> = (0..8)
        .map(|_| (0..trace_len).map(|_| rand_proth(&mut rng)).collect())
        .collect();
    let setup: Vec<Proth120> = (0..trace_len).map(|_| rand_proth(&mut rng)).collect();

    // --- random multilinear opening point z and the opening values (claims) ---
    let z: Vec<Proth120> = (0..N).map(|_| rand_proth(&mut rng)).collect();
    let wit_claims: Vec<Proth120> = witness
        .iter()
        .map(|p| evaluate_multivariate(p, &z, &worker))
        .collect();
    let setup_claims: Vec<Proth120> = vec![evaluate_multivariate(&setup, &z, &worker)];

    // --- commit each batch into its own Keccak256 tree (batch 8 + batch 1) ---
    let wit_refs: Vec<&[Proth120]> = witness.iter().map(|p| p.as_slice()).collect();
    let wit_oracle = commit_trace_part::<Proth120, Tree>(
        &wit_refs,
        &twiddles,
        lde_factor,
        FIRST_FOLD_LOG2,
        CAP_SIZE,
        N,
        &worker,
    );
    let setup_oracle = commit_trace_part::<Proth120, Tree>(
        &[setup.as_slice()],
        &twiddles,
        lde_factor,
        FIRST_FOLD_LOG2,
        CAP_SIZE,
        N,
        &worker,
    );
    // No separate memory batch in this configuration.
    let mem_oracle =
        commit_trace_part::<Proth120, Tree>(&[], &twiddles, lde_factor, FIRST_FOLD_LOG2, CAP_SIZE, N, &worker);

    // --- WHIR schedule: 6 rounds, fold by 1 each, RS codeword pinned to 2^13 ---
    // base LDE (round 0) = 32; subsequent LDE factors keep the codeword at 2^13
    // as the message folds down: message_r = 2^(8-r), lde_r = 2^13 / 2^(8-r).
    let schedule = WhirSchedule {
        base_lde_factor: lde_factor,
        cap_size: CAP_SIZE,
        whir_steps_schedule: vec![1, 1, 1, 1, 1, 1],
        whir_queries_schedule: vec![2, 2, 2, 2, 2, 2],
        whir_steps_lde_factors: vec![64, 128, 256, 512, 1024],
        whir_pow_schedule: vec![0, 0, 0, 0, 0, 0],
    };

    let batching_challenge = rand_proth(&mut rng);
    let mut seed_bytes = [0u8; 32];
    rng.fill(&mut seed_bytes);
    let seed = Keccak256Seed(seed_bytes);

    let proof = whir_fold::<Proth120, Proth120, Tree, Keccak256Transcript>(
        mem_oracle,
        vec![],
        wit_oracle,
        wit_claims.clone(),
        &setup_oracle,
        setup_claims.clone(),
        z.clone(),
        batching_challenge,
        &schedule,
        &twiddles,
        seed,
        CAP_SIZE,
        N,
        &worker,
    );

    // --- serialize EVM calldata (VARIANT 5 layout of whir.sol) ------------------
    // Byte layout consumed by the Solidity verifier, in order:
    //   preimage: [seed:32][batching:16 | opening:16][z: nz elems, 2/word]
    //             [witness cap: CAP*32][setup cap: CAP*32]
    //   per round r in 0..6:
    //     sumcheck poly: fold * (3 field els, 16B BE each)   (fold==1 here)
    //     r<5 (internal): next oracle cap (CAP*32) | ood_value:16 | pow nonce:8
    //                     then q queries; r==0 reads witness(8 cols)+setup(1 col),
    //                     r>=1 reads one extension column from the prior oracle.
    //     r==5 (final):   final monomials (2^rfin * 16B) | pow nonce:8 | q queries.
    //   each query: leaf values (concat 16B BE) then `depth` sibling digests (32B).
    let be16 = |e: Proth120| -> [u8; 16] { e.to_u128().to_be_bytes() };
    let dig32 = |d: &[u32; 8]| -> [u8; 32] {
        let mut o = [0u8; 32];
        for i in 0..8 {
            o[4 * i..4 * i + 4].copy_from_slice(&d[i].to_be_bytes());
        }
        o
    };
    let mut cd: Vec<u8> = Vec::new();
    let push_leaf = |cd: &mut Vec<u8>, vals: &[Proth120], path: &[[u32; 8]]| {
        for v in vals.iter() {
            cd.extend_from_slice(&be16(*v));
        }
        for d in path.iter() {
            cd.extend_from_slice(&dig32(d));
        }
    };
    // Base-layer leaves: `leaf_values_concatenated` is OFFSET-major
    // (result[offset][column] => [c0o0,c1o0,..,c0o1,c1o1,..]) but the committed
    // Keccak leaf hash is COLUMN-major (`for column { for offset }`). Transpose so
    // the EVM (which reads column-by-column, 2 values/word) hashes the same bytes.
    let push_base_leaf =
        |cd: &mut Vec<u8>, vals: &[Proth120], path: &[[u32; 8]], num_cols: usize| {
            let vp = vals.len() / num_cols;
            for c in 0..num_cols {
                for o in 0..vp {
                    cd.extend_from_slice(&be16(vals[o * num_cols + c]));
                }
            }
            for d in path.iter() {
                cd.extend_from_slice(&dig32(d));
            }
        };
    // preimage: seed
    cd.extend_from_slice(&seed_bytes);
    // batching || opening(batched claim = sum_i gamma^i * claim_i, witness then setup)
    cd.extend_from_slice(&be16(batching_challenge));
    let mut batched = Proth120::ZERO;
    let mut g = Proth120::ONE;
    for c in wit_claims.iter().chain(setup_claims.iter()) {
        let mut t = *c;
        t.mul_assign(&g);
        batched.add_assign(&t);
        g.mul_assign(&batching_challenge);
    }
    cd.extend_from_slice(&be16(batched));
    // z_initial (nz==8 even -> exactly nz*16 bytes)
    for e in z.iter() {
        cd.extend_from_slice(&be16(*e));
    }
    // base caps: witness (BCAP0) then setup (BCAP1)
    for d in proof.witness_commitment.commitment.cap.cap.iter() {
        cd.extend_from_slice(&dig32(d));
    }
    for d in proof.setup_commitment.commitment.cap.cap.iter() {
        cd.extend_from_slice(&dig32(d));
    }
    let plen = cd.len();
    // proof stream
    for r in 0..6usize {
        let sp = &proof.sumcheck_polys[r];
        cd.extend_from_slice(&be16(sp[0]));
        cd.extend_from_slice(&be16(sp[1]));
        cd.extend_from_slice(&be16(sp[2]));
        if r < 5 {
            for d in proof.intermediate_whir_oracles[r].commitment.cap.cap.iter() {
                cd.extend_from_slice(&dig32(d));
            }
            cd.extend_from_slice(&be16(proof.ood_samples[r]));
            cd.extend_from_slice(&proof.pow_nonces[r].to_be_bytes());
            for qq in 0..2usize {
                if r == 0 {
                    let wq = &proof.witness_commitment.queries[qq];
                    push_base_leaf(
                        &mut cd,
                        &wq.leaf_values_concatenated,
                        &wq.path,
                        proof.witness_commitment.num_columns,
                    );
                    let sq = &proof.setup_commitment.queries[qq];
                    push_base_leaf(
                        &mut cd,
                        &sq.leaf_values_concatenated,
                        &sq.path,
                        proof.setup_commitment.num_columns,
                    );
                } else {
                    let q = &proof.intermediate_whir_oracles[r - 1].queries[qq];
                    push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
                }
            }
        } else {
            for m in proof.final_monomials.iter() {
                cd.extend_from_slice(&be16(*m));
            }
            cd.extend_from_slice(&proof.pow_nonces[5].to_be_bytes());
            for qq in 0..2usize {
                let q = &proof.intermediate_whir_oracles[4].queries[qq];
                push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
            }
        }
    }
    // DEBUG: replay the round-0 transcript with the concrete Keccak transcript to
    // get the ground-truth pre-PoW seed + drawn query indices (should be [72,3756]).
    {
        use transcript::Transcript as _;
        type TR = Keccak256Transcript;
        let mut s = Keccak256Seed(seed_bytes);
        let sp = &proof.sumcheck_polys[0];
        TR::commit_extension_field_elements(&mut s, &[sp[0], sp[1], sp[2]]);
        let mut alpha = [Proth120::ZERO; 1];
        TR::draw_random_field_elements(&mut s, &mut alpha);
        let mut capwords = vec![];
        for d in proof.intermediate_whir_oracles[0].commitment.cap.cap.iter() {
            capwords.extend_from_slice(d);
        }
        TR::commit_u32_with_seed(&mut s, &capwords);
        let mut ood = [Proth120::ZERO; 1];
        TR::draw_random_field_elements(&mut s, &mut ood);
        TR::commit_extension_field_elements(&mut s, &[proof.ood_samples[0]]);
        eprintln!("REPLAY r0 pre-pow seed = {:02x?}", s.0);
        // draw_query_bits (pow=0): search_pow then draw_randomness, skip word 0
        let (_nonce, mut src) = {
            let (ns, nc) =
                <TR as Transcript<Proth120, Proth120>>::search_pow(&s, 0, &worker);
            s = ns;
            let num_bits = 2 * 12usize;
            let nrw = num_bits.next_multiple_of(32) / 32;
            let padded = (nrw + 1).next_multiple_of(8);
            let mut buf = vec![0u32; padded];
            TR::draw_randomness(&mut s, &mut buf);
            (nc, buf[1..].to_vec())
        };
        let mut idxs = vec![];
        for _ in 0..2 {
            let mut idx = 0usize;
            for b in 0..12 {
                let wi = (idxs.len() * 12 + b) / 32;
                let bi = (idxs.len() * 12 + b) % 32;
                idx |= (((src[wi] >> bi) & 1) as usize) << b;
            }
            idxs.push(idx);
        }
        let _ = &mut src;
        eprintln!("REPLAY r0 query indices = {idxs:?}");
    }

    // The EVM binds the preimage `cd[0..plen]` against storage slot 0; the forge
    // harness computes that keccak itself and `vm.store`s it before calling.
    let out_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../verifier_evm/whir/testdata");
    std::fs::create_dir_all(out_dir).unwrap();
    let hex: String = cd.iter().map(|b| format!("{b:02x}")).collect();
    std::fs::write(format!("{out_dir}/proth120_whir_calldata.hex"), &hex).unwrap();
    println!("wrote {} bytes of EVM calldata (plen={})", cd.len(), plen);

    // --- dump proof + auxiliary values to JSON ---
    // NOTE: the `serde_json::json!`/`Value` path cannot hold `u128`; we use a
    // derived-Serialize struct + `to_string`, whose serializer handles `u128`.
    // All field values are emitted as decimal strings of their *normal* form.
    #[derive(serde::Serialize)]
    struct Params {
        message_log2: usize,
        lde_log2: usize,
        codeword_log2: u32,
        cap_size: usize,
        num_witness_cols: usize,
        num_setup_cols: usize,
        folds: Vec<usize>,
        queries: Vec<usize>,
        pow: Vec<u32>,
    }
    #[derive(serde::Serialize)]
    struct Dump {
        params: Params,
        initial_seed: Vec<u8>,
        opening_point: Vec<String>,
        witness_claims: Vec<String>,
        setup_claims: Vec<String>,
        batching_challenge: String,
        proof: WhirPolyCommitProof<Proth120, Proth120, Tree>,
    }
    let to_dec = |e: &Proth120| e.to_u128().to_string();
    let dump = Dump {
        params: Params {
            message_log2: N,
            lde_log2: LDE_LOG2,
            codeword_log2: codeword.trailing_zeros(),
            cap_size: CAP_SIZE,
            num_witness_cols: 8,
            num_setup_cols: 1,
            folds: schedule.whir_steps_schedule.clone(),
            queries: schedule.whir_queries_schedule.clone(),
            pow: schedule.whir_pow_schedule.clone(),
        },
        initial_seed: seed_bytes.to_vec(),
        opening_point: z.iter().map(to_dec).collect(),
        witness_claims: wit_claims.iter().map(to_dec).collect(),
        setup_claims: setup_claims.iter().map(to_dec).collect(),
        batching_challenge: to_dec(&batching_challenge),
        proof,
    };

    let out_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../verifier_evm/whir/testdata");
    std::fs::create_dir_all(out_dir).unwrap();
    let path = format!("{out_dir}/proth120_whir_input.json");
    std::fs::write(&path, serde_json::to_string_pretty(&dump).unwrap()).unwrap();
    println!("wrote WHIR EVM input to {path}");
}
