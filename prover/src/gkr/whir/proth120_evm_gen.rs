//! Generates WHIR proof input data over `Proth120` with a Keccak256 transcript
//! and Keccak256 Merkle trees, matching the byte layout expected by the EVM
//! (Solidity) WHIR verifier, and dumps it to JSON for cross-checking.
//!
//! Two configurations share one schedule-driven generator [`run_generation`]:
//!   * `generate_whir_input_for_evm` — the small VARIANT-5 test schedule
//!     (message 2^8, LDE 32 => RS codeword 2^13, folds all 1, no PoW). Runs
//!     locally in milliseconds and is what `WhirRealProofTest` verifies.
//!   * `generate_whir_input_for_evm_production` (`#[ignore]`) — the VARIANT-4
//!     production schedule (message 2^26, RS codeword 2^31, folds [2,4,4,4,4,4],
//!     queries [17,12,8,6,5,4], PoW [30,30,27,25,21,24]). Needs a big machine
//!     (tens of GB, minutes); run it via `gen_whir_prod.sh`.
//!
//! The two base batches (8 columns + 1 column) are committed COSET-BY-COSET via
//! `CosetByCosetBaseCommitment`: each LDE coset is computed and hashed separately
//! (with in-coset parallelism) so the full RS codeword is never materialized, and
//! round-0 queries recompute only the coset they land in (fed to `whir_fold` via
//! its `base_query_hook`). The 8-column batch goes into the MEMORY oracle and the
//! single column into the WITNESS oracle (setup is empty): whir_fold takes those
//! by value and drops them right after the base layer, so their coset-0 data is
//! freed before the memory-heavy intermediate rounds (which are still built
//! monolithically inside `whir_fold` — the remaining memory item for 2^26).

use super::coset_commit::CosetByCosetBaseCommitment;
use super::*;
use crate::gkr::prover::stages::stage1::{commit_trace_part, ColumnMajorCosetBoundTracePart};
use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use field::Proth120;
use rand::{Rng, SeedableRng};
use std::alloc::Global;
use std::sync::Arc;
use transcript::{Keccak256Seed, Keccak256Transcript};

type Tree = Keccak256MerkleTreeWithCap<Global>;

const NUM_ROUNDS: usize = 6;
const NUM_WITNESS_COLS: usize = 8;

/// One WHIR generation configuration (a whir.sol VARIANT). All per-round vectors
/// have `NUM_ROUNDS` entries except `lde_factors`, which has `NUM_ROUNDS - 1` (the
/// oracles committed after each of rounds 0..5).
struct GenConfig {
    /// log2 of the message (per-column) size.
    message_log2: usize,
    /// log2 of the initial (round-0) LDE factor.
    base_lde_log2: usize,
    /// Merkle cap size (matches EVM `CAP`).
    cap_size: usize,
    /// folds per round; `folds[0]` is also the round-0 values-per-leaf log2.
    folds: Vec<usize>,
    /// number of queries per round.
    queries: Vec<usize>,
    /// LDE factors of the intermediate oracles (rounds 1..NUM_ROUNDS).
    lde_factors: Vec<usize>,
    /// PoW bits per round.
    pow: Vec<u32>,
    /// RNG seed (for reproducibility).
    rng_seed: u64,
    /// Output filename suffix (e.g. "" for VARIANT 5, "_prod" for VARIANT 4).
    out_suffix: &'static str,
}

fn rand_proth<R: Rng>(rng: &mut R) -> Proth120 {
    let lo: u64 = rng.random();
    let hi: u64 = rng.random();
    Proth120::new((((hi as u128) << 64) | lo as u128) % Proth120::ORDER)
}

/// Full generation: random polys -> coset-by-coset base commitment -> `whir_fold`
/// -> EVM calldata (+ JSON), written under `verifier_evm/whir/testdata`.
fn run_generation(cfg: &GenConfig, worker: &Worker) {
    assert_eq!(cfg.folds.len(), NUM_ROUNDS);
    assert_eq!(cfg.queries.len(), NUM_ROUNDS);
    assert_eq!(cfg.pow.len(), NUM_ROUNDS);
    assert_eq!(cfg.lde_factors.len(), NUM_ROUNDS - 1);

    let t0 = std::time::Instant::now();
    let log = |msg: &str| println!("[whir-gen +{:6.1}s] {msg}", t0.elapsed().as_secs_f64());
    println!(
        "[whir-gen] message 2^{}, LDE 2^{} => codeword 2^{}, {}+1 cols, cap {}",
        cfg.message_log2,
        cfg.base_lde_log2,
        cfg.message_log2 + cfg.base_lde_log2,
        NUM_WITNESS_COLS,
        cfg.cap_size,
    );
    println!(
        "[whir-gen] folds={:?} queries={:?} pow={:?}",
        cfg.folds, cfg.queries, cfg.pow
    );

    let n = cfg.message_log2;
    let first_fold_log2 = cfg.folds[0];
    let cap_size = cfg.cap_size;
    let lde_factor = 1usize << cfg.base_lde_log2;
    let trace_len = 1usize << n;
    let codeword = trace_len * lde_factor;

    let mut rng = rand::rngs::StdRng::seed_from_u64(cfg.rng_seed);
    // Twiddles are for the message-size NTT used per LDE coset.
    log("precomputing twiddles");
    let twiddles = fft::Twiddles::<Proth120, Global>::new(trace_len, worker);

    // --- 8 + 1 random polynomials (values on the boolean hypercube). The 8-column
    //     batch goes into the MEMORY oracle and the single column into the WITNESS
    //     oracle; the SETUP oracle is left empty. whir_fold takes mem/wit by value
    //     and drops them right after the base layer, whereas setup is borrowed and
    //     held for the whole call — so putting the big (8-col) batch in the owned
    //     memory oracle frees it before the memory-heavy intermediate rounds. The
    //     batching order (mem -> wit -> setup) keeps the 8-col batch first (gamma^0..7),
    //     so the EVM calldata is unchanged (BCAP0 = 8-col, BCAP1 = 1-col). ---
    log("generating random polynomials");
    let mem_polys: Vec<Vec<Proth120>> = (0..NUM_WITNESS_COLS)
        .map(|_| (0..trace_len).map(|_| rand_proth(&mut rng)).collect())
        .collect();
    let wit_poly: Vec<Proth120> = (0..trace_len).map(|_| rand_proth(&mut rng)).collect();

    // --- random multilinear opening point z and the opening values (claims) ---
    log("computing opening claims");
    let z: Vec<Proth120> = (0..n).map(|_| rand_proth(&mut rng)).collect();
    let mem_claims: Vec<Proth120> = mem_polys
        .iter()
        .map(|p| evaluate_multivariate(p, &z, worker))
        .collect();
    let wit_claims: Vec<Proth120> = vec![evaluate_multivariate(&wit_poly, &z, worker)];

    // --- commit each batch coset-by-coset (cosets computed separately, each with
    //     in-coset parallelism) so the full RS codeword is never materialized. ---
    let mem_refs: Vec<&[Proth120]> = mem_polys.iter().map(|p| p.as_slice()).collect();
    log("committing memory oracle (8 cols) coset-by-coset");
    let mem_commitment = CosetByCosetBaseCommitment::commit(
        &mem_refs,
        &twiddles,
        lde_factor,
        first_fold_log2,
        cap_size,
        n,
        worker,
    );
    log("committing witness oracle (1 col) coset-by-coset");
    let wit_commitment = CosetByCosetBaseCommitment::commit(
        &[wit_poly.as_slice()],
        &twiddles,
        lde_factor,
        first_fold_log2,
        cap_size,
        n,
        worker,
    );

    // Slim base oracle: whir_fold only reads coset 0 (main domain, for batching) and
    // the cap; round-0 queries are served by the coset-by-coset hook below.
    let build_slim =
        |c: &CosetByCosetBaseCommitment| -> ColumnMajorBaseOracleForLDE<Proth120, Tree> {
            let coset0 = ColumnMajorBaseOracleForCoset {
                original_values_normal_order: c
                    .main_domain_columns(&twiddles, worker)
                    .into_iter()
                    .map(|col| ColumnMajorCosetBoundTracePart {
                        column: Arc::new(col),
                        offset: Proth120::ONE,
                    })
                    .collect(),
                offset: Proth120::ONE,
                trace_len_log2: n,
            };
            let cap = c.get_cap();
            let cap_tree = Tree::continue_from_leaf_hashes(cap.cap.clone(), cap.cap.len(), worker);
            ColumnMajorBaseOracleForLDE {
                cosets: vec![coset0],
                tree: cap_tree,
                values_per_leaf: c.values_per_leaf,
                trace_len_log2: n,
            }
        };
    log("building slim base oracles (coset 0 + cap)");
    let mem_oracle = build_slim(&mem_commitment); // 8 cols, owned by whir_fold
    let wit_oracle = build_slim(&wit_commitment); // 1 col, owned by whir_fold
                                                  // empty setup oracle (borrowed, held for the whole call, but carries no cosets)
    let setup_oracle = commit_trace_part::<Proth120, Tree>(
        &[],
        &twiddles,
        lde_factor,
        first_fold_log2,
        cap_size,
        n,
        worker,
    );

    // set_idx: 0 = memory (8 cols), 1 = witness (1 col); setup (2) is empty.
    let base_query_hook = |set_idx: usize,
                           query_index: usize|
     -> (Vec<Vec<Proth120>>, BaseFieldQuery<Proth120, Tree>) {
        match set_idx {
            0 => mem_commitment.query_structured(query_index, &twiddles, worker),
            1 => wit_commitment.query_structured(query_index, &twiddles, worker),
            _ => unreachable!("only memory(0)/witness(1) base sets carry columns"),
        }
    };

    let schedule = WhirSchedule {
        base_lde_factor: lde_factor,
        cap_size,
        whir_steps_schedule: cfg.folds.clone(),
        whir_queries_schedule: cfg.queries.clone(),
        whir_steps_lde_factors: cfg.lde_factors.clone(),
        whir_pow_schedule: cfg.pow.clone(),
    };

    let batching_challenge = rand_proth(&mut rng);
    let mut seed_bytes = [0u8; 32];
    rng.fill(&mut seed_bytes);
    let seed = Keccak256Seed(seed_bytes);

    log("running whir_fold (folding rounds + PoW grinding)");
    let proof = whir_fold::<Proth120, Proth120, Tree, Keccak256Transcript>(
        mem_oracle,
        mem_claims.clone(),
        wit_oracle,
        wit_claims.clone(),
        &setup_oracle,
        vec![],
        z.clone(),
        batching_challenge,
        &schedule,
        &twiddles,
        seed,
        cap_size,
        n,
        Some(&base_query_hook),
        WhirIntermediateOracleMode::CosetByCoset,
        worker,
    );

    // --- serialize EVM calldata (whir.sol layout, schedule-driven) --------------
    // preimage: [seed:32][batching:16 | opening:16][z: nz*16]
    //           [witness cap: CAP*32][setup cap: CAP*32]
    // per round r: folds[r] sumcheck polys (3 * 16B);
    //   r<5 (internal): next oracle cap (CAP*32) | ood:16 | pow nonce:8, then
    //                   queries[r] queries (r==0: witness+setup base leaves,
    //                   r>=1: one extension leaf); depth sibling digests per query.
    //   r==5 (final):   final monomials (2^rfin * 16B) | pow nonce:8 | queries[5].
    log("serializing EVM calldata");
    let be16 = |e: Proth120| -> [u8; 16] { e.to_u128().to_be_bytes() };
    let dig32 = |d: &[u32; 8]| -> [u8; 32] {
        let mut o = [0u8; 32];
        for i in 0..8 {
            o[4 * i..4 * i + 4].copy_from_slice(&d[i].to_be_bytes());
        }
        o
    };
    let push_leaf = |cd: &mut Vec<u8>, vals: &[Proth120], path: &[[u32; 8]]| {
        for v in vals.iter() {
            cd.extend_from_slice(&be16(*v));
        }
        for d in path.iter() {
            cd.extend_from_slice(&dig32(d));
        }
    };
    // Base leaves: `leaf_values_concatenated` is OFFSET-major but the committed
    // Keccak leaf hash is COLUMN-major, so transpose to `[column][offset]`.
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

    let mut cd: Vec<u8> = Vec::new();
    cd.extend_from_slice(&seed_bytes);
    cd.extend_from_slice(&be16(batching_challenge));
    // opening value = batched claim = sum_i gamma^i * claim_i (8-col batch then 1-col)
    let mut batched = Proth120::ZERO;
    let mut g = Proth120::ONE;
    for c in mem_claims.iter().chain(wit_claims.iter()) {
        let mut t = *c;
        t.mul_assign(&g);
        batched.add_assign(&t);
        g.mul_assign(&batching_challenge);
    }
    cd.extend_from_slice(&be16(batched));
    // z_initial: nz elements (nz even for both variants -> exactly nz*16 bytes)
    assert!(
        n % 2 == 0,
        "odd nz would need padding to the EVM's ceil(nz/2) words"
    );
    for e in z.iter() {
        cd.extend_from_slice(&be16(*e));
    }
    // BCAP0 = 8-col batch (memory oracle), BCAP1 = 1-col batch (witness oracle)
    for d in mem_commitment.get_cap().cap.iter() {
        cd.extend_from_slice(&dig32(d));
    }
    for d in wit_commitment.get_cap().cap.iter() {
        cd.extend_from_slice(&dig32(d));
    }
    let plen = cd.len();

    let mut sc = 0usize; // sumcheck-poly cursor into proof.sumcheck_polys
    for r in 0..NUM_ROUNDS {
        for _ in 0..cfg.folds[r] {
            let sp = &proof.sumcheck_polys[sc];
            sc += 1;
            cd.extend_from_slice(&be16(sp[0]));
            cd.extend_from_slice(&be16(sp[1]));
            cd.extend_from_slice(&be16(sp[2]));
        }
        if r < NUM_ROUNDS - 1 {
            for d in proof.intermediate_whir_oracles[r].commitment.cap.cap.iter() {
                cd.extend_from_slice(&dig32(d));
            }
            cd.extend_from_slice(&be16(proof.ood_samples[r]));
            cd.extend_from_slice(&proof.pow_nonces[r].to_be_bytes());
            for qq in 0..cfg.queries[r] {
                if r == 0 {
                    // BCAP0 = 8-col batch (memory oracle), then BCAP1 = 1-col (witness).
                    let mq = &proof.memory_commitment.queries[qq];
                    push_base_leaf(
                        &mut cd,
                        &mq.leaf_values_concatenated,
                        &mq.path,
                        proof.memory_commitment.num_columns,
                    );
                    let wq = &proof.witness_commitment.queries[qq];
                    push_base_leaf(
                        &mut cd,
                        &wq.leaf_values_concatenated,
                        &wq.path,
                        proof.witness_commitment.num_columns,
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
            cd.extend_from_slice(&proof.pow_nonces[r].to_be_bytes());
            for qq in 0..cfg.queries[r] {
                let q = &proof.intermediate_whir_oracles[NUM_ROUNDS - 2].queries[qq];
                push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
            }
        }
    }

    // The EVM binds the preimage `cd[0..plen]` against storage slot 0; the forge
    // harness computes that keccak itself and `vm.store`s it before calling.
    let out_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../verifier_evm/whir/testdata");
    std::fs::create_dir_all(out_dir).unwrap();
    let suffix = cfg.out_suffix;
    let hex: String = cd.iter().map(|b| format!("{b:02x}")).collect();
    std::fs::write(
        format!("{out_dir}/proth120_whir_calldata{suffix}.hex"),
        &hex,
    )
    .unwrap();
    log(&format!(
        "wrote {} bytes of EVM calldata (plen={}, message 2^{})",
        cd.len(),
        plen,
        n
    ));

    // --- dump proof + auxiliary values to JSON (u128 via derived Serialize) ------
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
            message_log2: n,
            lde_log2: cfg.base_lde_log2,
            codeword_log2: codeword.trailing_zeros(),
            cap_size,
            num_witness_cols: NUM_WITNESS_COLS,
            num_setup_cols: 1,
            folds: schedule.whir_steps_schedule.clone(),
            queries: schedule.whir_queries_schedule.clone(),
            pow: schedule.whir_pow_schedule.clone(),
        },
        initial_seed: seed_bytes.to_vec(),
        opening_point: z.iter().map(to_dec).collect(),
        // EVM view: the 8-col batch is BCAP0, the 1-col batch is BCAP1 (prover-side
        // these live in the memory and witness oracles respectively).
        witness_claims: mem_claims.iter().map(to_dec).collect(),
        setup_claims: wit_claims.iter().map(to_dec).collect(),
        batching_challenge: to_dec(&batching_challenge),
        proof,
    };
    log("writing proof JSON");
    let path = format!("{out_dir}/proth120_whir_input{suffix}.json");
    std::fs::write(&path, serde_json::to_string_pretty(&dump).unwrap()).unwrap();
    log(&format!("done, wrote {path}"));
}

/// VARIANT 5 (whir.sol): small test schedule, runs locally; matches the fixture
/// verified by `WhirRealProofTest`.
#[test]
fn generate_whir_input_for_evm() {
    let worker = Worker::new_with_num_threads(1);
    let cfg = GenConfig {
        message_log2: 8,
        base_lde_log2: 5,
        cap_size: 8,
        folds: vec![1, 1, 1, 1, 1, 1],
        queries: vec![2, 2, 2, 2, 2, 2],
        lde_factors: vec![64, 128, 256, 512, 1024],
        pow: vec![0, 0, 0, 0, 0, 0],
        rng_seed: 0xC0FFEE,
        out_suffix: "",
    };
    run_generation(&cfg, &worker);
}

/// Smoke test of the folds>1 / queries>2 / PoW>0 path end-to-end (message 2^10).
/// There is no EVM VARIANT for this shape, so we only assert the whole pipeline
/// (coset-by-coset commit with vp=4, `whir_fold` folding by 2, parallel PoW,
/// schedule-driven serializer) runs and emits a non-empty calldata file.
#[test]
fn generate_whir_smoke_folds_gt1() {
    let worker = Worker::new_with_num_threads(4);
    let cfg = GenConfig {
        message_log2: 10,
        base_lde_log2: 5, // codeword pinned to 2^15
        cap_size: 8,
        folds: vec![2, 2, 1, 1, 1, 1], // sum 6 => final 2^4 monomials
        queries: vec![3, 3, 2, 2, 2, 2],
        lde_factors: vec![128, 512, 1024, 2048, 4096],
        pow: vec![2, 0, 0, 0, 0, 0],
        rng_seed: 0x5EED,
        out_suffix: "_smoke",
    };
    run_generation(&cfg, &worker);

    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../verifier_evm/whir/testdata");
    let hex = format!("{dir}/proth120_whir_calldata_smoke.hex");
    assert!(std::fs::metadata(&hex).unwrap().len() > 0);
    // clean up the smoke artifacts (not an EVM fixture).
    let _ = std::fs::remove_file(&hex);
    let _ = std::fs::remove_file(format!("{dir}/proth120_whir_input_smoke.json"));
}

/// VARIANT 4 (whir.sol): production schedule, message 2^26 => RS codeword 2^31.
/// HEAVY — tens of GB of RAM and minutes of PoW/FFT. Ignored by default; run via
/// `gen_whir_prod.sh` (release mode, all cores).
#[test]
#[ignore = "production-sized (2^26): needs a big machine; run gen_whir_prod.sh"]
fn generate_whir_input_for_evm_production() {
    let worker = Worker::new();
    let cfg = GenConfig {
        message_log2: 26,
        base_lde_log2: 5,
        cap_size: 8,
        // folds sum to 22 => final poly 2^(26-22) = 2^4 = 16 monomials.
        folds: vec![2, 4, 4, 4, 4, 4],
        queries: vec![17, 12, 8, 6, 5, 4],
        // codeword pinned to 2^31: lde_r = 2^(31 - message_r) = 2^(5 + prefolds).
        lde_factors: vec![
            1 << 7,  // 128
            1 << 11, // 2048
            1 << 15, // 32768
            1 << 19, // 524288
            1 << 23, // 8388608
        ],
        pow: vec![30, 30, 27, 25, 21, 24],
        rng_seed: 0xC0FFEE,
        out_suffix: "_prod",
    };
    run_generation(&cfg, &worker);
}
