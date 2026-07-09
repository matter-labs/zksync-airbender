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
use crate::gkr::prover::stages::commitment_utils::{
    commit_trace_part, ColumnMajorCosetBoundTracePart,
};
use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use field::Proth120;
use rand::{Rng, SeedableRng};
use std::alloc::Global;
use std::sync::Arc;
use transcript::{Keccak256Seed, Keccak256Transcript};

type Tree = Keccak256MerkleTreeWithCap<Global>;

const NUM_WITNESS_COLS: usize = 8;

/// One WHIR generation configuration (a whir.sol VARIANT). The number of rounds is
/// `folds.len()`; `queries`/`pow` have the same length, and `lde_factors` has one
/// fewer (one per intermediate oracle, committed after each of rounds `0..len-1`).
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
    /// LDE factors of the intermediate oracles (one per round after the first).
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
    let num_rounds = cfg.folds.len();
    assert!(num_rounds >= 2, "WHIR needs at least 2 rounds");
    assert_eq!(cfg.queries.len(), num_rounds);
    assert_eq!(cfg.pow.len(), num_rounds);
    assert_eq!(cfg.lde_factors.len(), num_rounds - 1);

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
    let mem_commitment = CosetByCosetBaseCommitment::<Proth120, Tree>::commit(
        &mem_refs,
        &twiddles,
        lde_factor,
        first_fold_log2,
        cap_size,
        n,
        worker,
    );
    log("committing witness oracle (1 col) coset-by-coset");
    let wit_commitment = CosetByCosetBaseCommitment::<Proth120, Tree>::commit(
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
        |c: &CosetByCosetBaseCommitment<Proth120, Tree>| -> ColumnMajorBaseOracleForLDE<Proth120, Tree> {
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
                coset_size_log2: n,
            };
            let cap = c.get_cap();
            let cap_tree = Tree::continue_from_leaf_hashes(cap.cap.clone(), cap.cap.len(), worker);
            ColumnMajorBaseOracleForLDE {
                cosets: vec![coset0],
                tree: cap_tree,
                values_per_leaf: c.values_per_leaf,
                coset_size_log2: n,
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
    for r in 0..num_rounds {
        for _ in 0..cfg.folds[r] {
            let sp = &proof.sumcheck_polys[sc];
            sc += 1;
            cd.extend_from_slice(&be16(sp[0]));
            cd.extend_from_slice(&be16(sp[1]));
            cd.extend_from_slice(&be16(sp[2]));
        }
        if r < num_rounds - 1 {
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
                let q = &proof.intermediate_whir_oracles[num_rounds - 2].queries[qq];
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

/// Compute a WHIR schedule in the SAME mode as VARIANT 4 — 100-bit security under
/// the pessimistic conjecture (20% query margin), PoW capped at 30 bits — for a
/// given folding plan, keeping every RS codeword pinned at `2^max_codeword_log2`.
///
/// Per round with LDE-bit count `cb` (= log2 of that round's oracle LDE factor):
///   q   = ceil(1.2 * (100 - 30) / cb)            // queries at the max PoW
///   pow = clamp(ceil(100 - q*cb/1.2), 0, 30)     // smallest PoW that keeps that q
/// which reproduces VARIANT 4's `[17,12,8,6,5,4]` / `[30,30,27,25,21,24]` for its
/// `cb = [5,7,11,15,19,23]`.
///
/// Folding plan: fold by `2^first_fold_log2` first, then by `2^fold_log2` while that
/// does not overshoot the `2^final_log2` target (the last fold shrinks to land on it).
fn pessimistic_config(
    message_log2: usize,
    first_lde_log2: usize,
    first_fold_log2: usize,
    fold_log2: usize,
    max_codeword_log2: usize,
    final_log2: usize,
    out_suffix: &'static str,
) -> GenConfig {
    assert!(final_log2 < message_log2 && first_fold_log2 >= 1 && fold_log2 >= 1);

    // folding plan: fold by 2^first_fold, then by 2^fold_log2 while it won't overshoot.
    let mut folds = vec![first_fold_log2];
    let mut folded = message_log2 - first_fold_log2;
    while folded > final_log2 {
        let f = fold_log2.min(folded - final_log2);
        folds.push(f);
        folded -= f;
    }
    assert_eq!(folded, final_log2);

    config_from_folds(
        message_log2,
        first_lde_log2,
        folds,
        max_codeword_log2,
        out_suffix,
    )
}

/// Compute a `GenConfig` in the pessimistic-conjecture mode (100-bit security, PoW
/// capped at 30, 20% margin) for an EXPLICIT per-round folding plan, keeping every RS
/// codeword pinned at `2^max_codeword_log2`. Used for non-uniform schedules.
fn config_from_folds(
    message_log2: usize,
    first_lde_log2: usize,
    folds: Vec<usize>,
    max_codeword_log2: usize,
    out_suffix: &'static str,
) -> GenConfig {
    const SECURITY: f64 = 100.0;
    const MAX_POW: f64 = 30.0;
    const MARGIN: f64 = 1.2; // pessimistic conjecture: +20% queries

    assert_eq!(
        message_log2 + first_lde_log2,
        max_codeword_log2,
        "first LDE must pin the base codeword to the max size"
    );
    assert!(folds.iter().all(|&f| f >= 1));
    assert!(folds.iter().sum::<usize>() < message_log2);
    let num_rounds = folds.len();

    // per-round LDE-bit count `cb` + intermediate-oracle LDE factors (codeword pinned)
    let mut cb = Vec::with_capacity(num_rounds);
    cb.push(first_lde_log2 as u32);
    let mut lde_factors = Vec::with_capacity(num_rounds - 1);
    let mut folded = message_log2;
    for &f in folds.iter().take(num_rounds - 1) {
        folded -= f;
        let lde_log2 = max_codeword_log2 - folded;
        lde_factors.push(1usize << lde_log2);
        cb.push(lde_log2 as u32);
    }

    // queries + PoW per round (pessimistic, 100-bit, PoW <= 30)
    let mut queries = Vec::with_capacity(num_rounds);
    let mut pow = Vec::with_capacity(num_rounds);
    for &c in cb.iter() {
        let c = c as f64;
        let q = (MARGIN * (SECURITY - MAX_POW) / c).ceil();
        let p = (SECURITY - q * c / MARGIN).ceil().clamp(0.0, MAX_POW);
        queries.push(q as usize);
        pow.push(p as u32);
    }

    GenConfig {
        message_log2,
        base_lde_log2: first_lde_log2,
        cap_size: 8,
        folds,
        queries,
        lde_factors,
        pow,
        rng_seed: 0xC0FFEE,
        out_suffix,
    }
}

/// Fast check (no proving): the schedule computer reproduces VARIANT 4 exactly for
/// its parameters (proving it is the same mode) and yields the expected aggressive
/// schedule, which meets 100-bit security every round.
#[test]
fn pessimistic_config_reproduces_variant4_and_aggressive() {
    // VARIANT 4 parameters -> the hand-written production schedule, byte for byte.
    let v4 = pessimistic_config(26, 5, 2, 4, 31, 4, "_check");
    assert_eq!(v4.folds, vec![2, 4, 4, 4, 4, 4]);
    assert_eq!(v4.queries, vec![17, 12, 8, 6, 5, 4]);
    assert_eq!(v4.pow, vec![30, 30, 27, 25, 21, 24]);
    assert_eq!(v4.lde_factors, vec![128, 2048, 32768, 524288, 8388608]);

    // Aggressive v1: first fold 8, then 32/32/32/16 (uniform builder). 16 final coeffs.
    let v1 = pessimistic_config(26, 6, 3, 5, 32, 4, "_agg");
    assert_eq!(v1.folds, vec![3, 5, 5, 5, 4]);
    assert_eq!(v1.queries, vec![14, 10, 6, 5, 4]);
    assert_eq!(v1.pow, vec![30, 25, 30, 21, 20]);
    assert_eq!(v1.lde_factors, vec![1 << 9, 1 << 14, 1 << 19, 1 << 24]);
    assert_eq!(v1.folds.iter().sum::<usize>(), 26 - 4); // 2^4 = 16 coeffs

    // Aggressive v2: fold by 2, then 16, then 32/32/32 (explicit non-uniform). 64 coeffs.
    let v2 = config_from_folds(26, 6, vec![1, 4, 5, 5, 5], 32, "_agg2");
    assert_eq!(v2.folds, vec![1, 4, 5, 5, 5]);
    assert_eq!(v2.queries, vec![14, 12, 8, 6, 4]);
    assert_eq!(v2.pow, vec![30, 30, 27, 20, 30]);
    assert_eq!(v2.lde_factors, vec![1 << 7, 1 << 11, 1 << 16, 1 << 21]);
    assert_eq!(v2.folds.iter().sum::<usize>(), 26 - 6); // 2^6 = 64 coeffs

    // every round of each must reach 100-bit security: pow + q*cb/1.2 >= 100.
    for (cfg, cbs) in [
        (&v1, vec![6.0f64, 9.0, 14.0, 19.0, 24.0]),
        (&v2, vec![6.0, 7.0, 11.0, 16.0, 21.0]),
    ] {
        for (i, &cb) in cbs.iter().enumerate() {
            let bits = cfg.pow[i] as f64 + cfg.queries[i] as f64 * cb / 1.2;
            assert!(bits >= 100.0 - 1e-9, "round {i}: only {bits} bits");
        }
    }
}

/// Small analogue of the aggressive config (message 2^12, base codeword 2^16): a
/// LARGER first fold, aggressive folding after, a codeword pinned at the max, and a
/// variable (non-6) round count — exercising `run_generation`'s round-agnostic path
/// end-to-end (whir_fold + schedule-driven serializer) cheaply.
#[test]
fn generate_whir_smoke_aggressive() {
    let worker = Worker::new_with_num_threads(4);
    let cfg = pessimistic_config(12, 4, 2, 3, 16, 3, "_aggsmoke");
    println!(
        "[agg-smoke] rounds={} folds={:?} queries={:?} pow={:?} lde={:?}",
        cfg.folds.len(),
        cfg.folds,
        cfg.queries,
        cfg.pow,
        cfg.lde_factors
    );
    run_generation(&cfg, &worker);
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../verifier_evm/whir/testdata");
    let hex = format!("{dir}/proth120_whir_calldata_aggsmoke.hex");
    assert!(std::fs::metadata(&hex).unwrap().len() > 0);
    let _ = std::fs::remove_file(&hex);
    let _ = std::fs::remove_file(format!("{dir}/proth120_whir_input_aggsmoke.json"));
}

/// Aggressive-folding production config: same 8+1 polys of 2^26 as VARIANT 4, first
/// LDE 64 (=> base codeword 2^32), first fold by 8 then fold by 32 while possible down
/// to 16 final coefficients, every RS codeword pinned at 2^32. 100-bit pessimistic
/// security, PoW capped at 30 bits. EVM verifier: `whir_agg.sol` / `WhirVerifierAgg`.
///   folds   = [3, 5, 5, 5, 4]   (fold by 8, 32, 32, 32, 16 => 2^4 = 16 final)
///   cb      = [6, 9, 14, 19, 24]   q = [14, 10, 6, 5, 4]   pow = [30, 25, 30, 21, 20]
/// HEAVY (2^32 codewords) — ignored by default; run via `gen_whir_agg.sh`.
#[test]
#[ignore = "aggressive production-sized (2^32 codewords): needs a big machine; run gen_whir_agg.sh"]
fn generate_whir_input_for_evm_aggressive() {
    let worker = Worker::new();
    let cfg = pessimistic_config(26, 6, 3, 5, 32, 4, "_agg");
    println!(
        "[whir-agg] folds={:?} queries={:?} pow={:?} lde_factors={:?}",
        cfg.folds, cfg.queries, cfg.pow, cfg.lde_factors
    );
    run_generation(&cfg, &worker);
}

/// Aggressive schedule v2 — same 8+1 polys of 2^26 and codeword pinned at 2^32, but
/// fold by 2 in the FIRST round only (keeps the expensive 8-column base leaf small —
/// see the proof-size analysis), then by 2^4, then aggressively by 2^5. Total 5 rounds,
/// sum of folds 20 => 2^(26-20) = 2^6 = 64 final coefficients (a LARGER final poly than
/// v1's 16, trading a bigger final-aggregate for smaller openings / a smaller proof).
/// EVM verifier: `whir_agg2.sol` / `WhirVerifierAgg2`.
///   folds   = [1, 4, 5, 5, 5]   (fold by 2, 16, 32, 32, 32 => 2^6 = 64 final)
///   cb      = [6, 7, 11, 16, 21]   q = [14, 12, 8, 6, 4]   pow = [30, 30, 27, 20, 30]
///   lde     = [128, 2048, 65536, 2097152]   final = 64 monomials (rfin 6)
/// HEAVY (2^32 codewords) — ignored by default; run via `gen_whir_agg2.sh`.
#[test]
#[ignore = "aggressive-v2 production-sized (2^32 codewords): needs a big machine; run gen_whir_agg2.sh"]
fn generate_whir_input_for_evm_aggressive_v2() {
    let worker = Worker::new();
    let cfg = config_from_folds(
        26,                  // message_log2 (same input polys as VARIANT 4)
        6,                   // first LDE factor 64 => base codeword 2^32
        vec![1, 4, 5, 5, 5], // fold by 2, then 16, then 32/32/32 => 64 final coeffs
        32,                  // max RS codeword 2^32
        "_agg2",
    );
    println!(
        "[whir-agg2] folds={:?} queries={:?} pow={:?} lde_factors={:?} final=2^{}",
        cfg.folds,
        cfg.queries,
        cfg.pow,
        cfg.lde_factors,
        cfg.message_log2 - cfg.folds.iter().sum::<usize>(),
    );
    run_generation(&cfg, &worker);
}
