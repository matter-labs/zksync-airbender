//! Production-scale backend parity: the target-recommended
//! [`DefaultBabyBearBackend`] must produce exactly the same base-commit LDE
//! output as [`NaiveBackend`] (proofs must not depend on the backend choice).
//!
//! The small-shape parity suite lives in `prover::gkr::prover::backend::tests`;
//! this test pins the SAME contract at a production-sized 2^20 hypercube,
//! where the work-stealing planner and the aarch64 NEON kernels take their
//! large-input branches. On aarch64 this compares the NEON backend (with its
//! combined-twiddle tables) against the naive path; elsewhere
//! `DefaultBabyBearBackend` resolves to the generic work-stealing backend.
//!
//!   cargo test -p experiments_runner --release backend_parity -- --nocapture

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::Rand;
use prover::gkr::prover::stages::commitment_utils::ColumnMajorCosetBoundTracePart;
use prover::gkr::prover::{Backend, DefaultBabyBearBackend, NaiveBackend};
use worker::Worker;

const N_LOG: usize = 20;
const NUM_COLS: usize = 4;
const LDE_FACTOR: usize = 2;
const NUM_THREADS: usize = 8;

fn check_equal_cosets(
    a: &[Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>],
    b: &[Vec<ColumnMajorCosetBoundTracePart<BabyBearField, BabyBearField>>],
) {
    assert_eq!(a.len(), LDE_FACTOR);
    assert_eq!(a.len(), b.len());
    for (coset_idx, (coset_a, coset_b)) in a.iter().zip(b.iter()).enumerate() {
        assert_eq!(coset_a.len(), NUM_COLS);
        assert_eq!(coset_a.len(), coset_b.len());
        for (col_idx, (ca, cb)) in coset_a.iter().zip(coset_b.iter()).enumerate() {
            assert_eq!(
                ca.offset, cb.offset,
                "offset mismatch at coset {coset_idx} column {col_idx}"
            );
            assert_eq!(ca.column.len(), 1 << N_LOG);
            assert_eq!(
                &ca.column[..],
                &cb.column[..],
                "column values mismatch at coset {coset_idx} column {col_idx}"
            );
        }
    }
}

#[test]
fn default_babybear_backend_lde_matches_naive_at_2_20() {
    let worker = Worker::new_with_num_threads(NUM_THREADS);
    let n = 1usize << N_LOG;

    let mut rng = rand::rng();
    let cols: Vec<Vec<BabyBearField>> = (0..NUM_COLS)
        .map(|_| (0..n).map(|_| BabyBearField::random_element(&mut rng)).collect())
        .collect();
    let col_refs: Vec<&[BabyBearField]> = cols.iter().map(|c| &c[..]).collect();

    // Each backend builds its own twiddle set (the NEON one carries extra
    // combined tables on top of the plain radix-2 ones).
    let default_backend = DefaultBabyBearBackend::default();
    let default_twiddles = Backend::<BabyBearField, BabyBearExt4>::make_twiddles(
        &default_backend,
        n,
        &worker,
    );
    let naive_twiddles =
        Backend::<BabyBearField, BabyBearExt4>::make_twiddles(&NaiveBackend, n, &worker);

    let got = Backend::<BabyBearField, BabyBearExt4>::lde_multiple_polys_from_hypercubes(
        &default_backend,
        &col_refs,
        &default_twiddles,
        LDE_FACTOR,
        &worker,
    );
    let reference = Backend::<BabyBearField, BabyBearExt4>::lde_multiple_polys_from_hypercubes(
        &NaiveBackend,
        &col_refs,
        &naive_twiddles,
        LDE_FACTOR,
        &worker,
    );

    check_equal_cosets(&reference, &got);
    println!(
        "[parity] DefaultBabyBearBackend == NaiveBackend on {NUM_COLS} cols x 2^{N_LOG}, lde {LDE_FACTOR}"
    );
}
