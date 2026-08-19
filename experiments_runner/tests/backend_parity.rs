#![feature(allocator_api)]
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
        .map(|_| {
            (0..n)
                .map(|_| BabyBearField::random_element(&mut rng))
                .collect()
        })
        .collect();
    let col_refs: Vec<&[BabyBearField]> = cols.iter().map(|c| &c[..]).collect();

    // Each backend builds its own twiddle set (the NEON one carries extra
    // combined tables on top of the plain radix-2 ones).
    let default_backend = DefaultBabyBearBackend::default();
    let default_twiddles =
        Backend::<BabyBearField, BabyBearExt4>::make_twiddles(&default_backend, n, &worker);
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

/// The production base-commit pipeline (what [`NaiveBackend`] runs per coset)
/// is scaled-copy (distribute powers) -> BITREVERSE -> CT NTT (bitreversed
/// input, natural output). The bitreversal pass is pure data movement, so a
/// commitment that stores the codeword in BITREVERSED order can skip it: feed
/// the scaled coefficients DIRECTLY (natural order) into the
/// natural->bitreversed CT kernel with the SAME bitreversed twiddle table.
/// This test pins the ordering fact behind that variant — per coset, the
/// alternative equals the naive codeword up to the in-coset bitreversal
/// permutation (and nothing else: same offsets, same values).
#[test]
fn no_bitreverse_lde_matches_naive_up_to_in_coset_bitreversal() {
    use field::Field;
    use prover::fft;
    use prover::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs;
    use std::alloc::Global;

    let n = 1usize << N_LOG;
    let log_n = n.trailing_zeros();
    let worker = Worker::new_with_num_threads(NUM_THREADS);

    let mut rng = rand::rng();
    let poly: Vec<BabyBearField> = (0..n)
        .map(|_| BabyBearField::random_element(&mut rng))
        .collect();

    let twiddles = fft::Twiddles::<BabyBearField, Global>::new(n, &worker);

    // Reference: the naive backend's RS codeword (natural-order evaluations).
    let reference = Backend::<BabyBearField, BabyBearExt4>::lde_multiple_polys_from_hypercubes(
        &NaiveBackend,
        &[&poly[..]],
        &twiddles,
        LDE_FACTOR,
        &worker,
    );

    // Alternative commitment (serial): same hypercube->monomial and
    // distribute-powers steps, NO bitreversal pass afterwards — the
    // natural->bitreversed kernel consumes the scaled coefficients as they
    // are and emits the evaluations in bitreversed enumeration.
    let mut coeffs = poly.clone();
    multivariate_hypercube_evals_into_coeffs(&mut coeffs, log_n);
    let next_root = fft::domain_generator_for_size::<BabyBearField>((n * LDE_FACTOR) as u64);
    let offsets = fft::materialize_powers_serial_starting_with_one::<BabyBearField, Global>(
        next_root, LDE_FACTOR,
    );
    let selected_twiddles = &twiddles.forward_twiddles[..n / 2];

    for (coset_idx, offset) in offsets.iter().enumerate() {
        let mut alt = coeffs.clone();
        if coset_idx != 0 {
            fft::distribute_powers_serial(&mut alt, BabyBearField::ONE, *offset);
        }
        fft::naive::serial_ct_ntt_natural_to_bitreversed(&mut alt[..], log_n, selected_twiddles);

        let reference_part = &reference[coset_idx][0];
        assert_eq!(reference_part.offset, *offset);
        // undo the alternative's bitreversed enumeration; values must then
        // match the natural-order reference codeword exactly
        fft::bitreverse_enumeration_inplace(&mut alt[..]);
        if alt[..] != reference_part.column[..] {
            let idx = alt
                .iter()
                .zip(reference_part.column.iter())
                .position(|(a, b)| a != b);
            panic!("coset {coset_idx}: first mismatch at index {idx:?}");
        }
    }
    println!(
        "[parity] no-bitreverse LDE == naive LDE up to in-coset bitreversal (2^{N_LOG}, lde {LDE_FACTOR})"
    );
}

/// Pin the exact relationship between the two serial NTT kernels.
///
/// `serial_ct_ntt_natural_to_bitreversed` (distance n/2->1, butterfly
/// `(u + s*v, u - s*v)` — twiddle on the input edge) and
/// `serial_ct_ntt_bitreversed_to_natural` (distance 1->n/2, butterfly
/// `(u + v, (u - v)*s)` — twiddle on the output edge) are TRANSPOSED butterfly
/// networks sharing the same bitreversed twiddle table. With `R` the
/// bitreversal permutation and `F` the DFT matrix (`F[i][j] = w^(i*j)`), this
/// test asserts, by building each kernel's full matrix on unit vectors:
///
///   1. b2n(x, T_br) == F(R(x))          (map F.R: bitreversed-INPUT reading)
///   2. n2b(x, T_br) == R(F(x))          (map R.F: bitreversed-OUTPUT writing)
///   3. n2b(x, T_br) == R(b2n(R(x), T_br))  — the only "same values" bridge:
///      same twiddles, but the ARRAY input must be re-enumerated too.
///   4. NO twiddle re-ordering makes one kernel compute the other's map:
///      with the natural-order table the stage-local prefix `T[..num_groups]`
///      no longer contains the right twiddle SET (the bitreversed table's
///      prefix property is what makes each prefix a valid smaller-domain
///      table), so b2n(., T_nat) / n2b(., T_nat) are not F composed with ANY
///      input/output permutation — checked exhaustively against all column
///      and row permutations of F.
#[test]
fn ntt_kernel_pair_is_transposed_not_twiddle_reorderable() {
    use field::Field;
    use prover::fft;
    use std::alloc::Global;

    const LOG_N: u32 = 4;
    let n = 1usize << LOG_N;
    let worker = Worker::new_with_num_threads(1);
    let twiddles = fft::Twiddles::<BabyBearField, Global>::new(n, &worker);
    let t_br = &twiddles.forward_twiddles[..n / 2];
    let t_nat = &twiddles.forward_twiddles_not_bitreversed[..n / 2];

    // reference DFT matrix
    let omega = fft::domain_generator_for_size::<BabyBearField>(n as u64);
    let omega_pows =
        fft::materialize_powers_serial_starting_with_one::<BabyBearField, Global>(omega, n);
    let f_matrix: Vec<Vec<BabyBearField>> = (0..n)
        .map(|i| (0..n).map(|j| omega_pows[(i * j) % n]).collect())
        .collect();
    let apply_f = |x: &[BabyBearField]| -> Vec<BabyBearField> {
        f_matrix
            .iter()
            .map(|row| {
                let mut acc = BabyBearField::ZERO;
                for (r, v) in row.iter().zip(x.iter()) {
                    let mut t = *r;
                    t.mul_assign(v);
                    acc.add_assign(&t);
                }
                acc
            })
            .collect()
    };
    let bitrev = |x: &[BabyBearField]| -> Vec<BabyBearField> {
        let mut y = x.to_vec();
        fft::bitreverse_enumeration_inplace(&mut y);
        y
    };

    let b2n = |x: &[BabyBearField], t: &[BabyBearField]| -> Vec<BabyBearField> {
        let mut y = x.to_vec();
        fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut y, LOG_N, t);
        y
    };
    let n2b = |x: &[BabyBearField], t: &[BabyBearField]| -> Vec<BabyBearField> {
        let mut y = x.to_vec();
        fft::naive::serial_ct_ntt_natural_to_bitreversed(&mut y, LOG_N, t);
        y
    };

    // matrix of a kernel via unit vectors: columns of the map
    let matrix_of =
        |f: &dyn Fn(&[BabyBearField]) -> Vec<BabyBearField>| -> Vec<Vec<BabyBearField>> {
            let mut cols = Vec::with_capacity(n);
            for j in 0..n {
                let mut e = vec![BabyBearField::ZERO; n];
                e[j] = BabyBearField::ONE;
                cols.push(f(&e));
            }
            cols // cols[j][i] = M[i][j]
        };

    // random probe for the exact identities 1-3
    let mut rng = rand::rng();
    let x: Vec<BabyBearField> = (0..n)
        .map(|_| BabyBearField::random_element(&mut rng))
        .collect();

    assert_eq!(b2n(&x, t_br), apply_f(&bitrev(&x)), "b2n(T_br) != F∘R");
    assert_eq!(n2b(&x, t_br), bitrev(&apply_f(&x)), "n2b(T_br) != R∘F");
    assert_eq!(
        n2b(&x, t_br),
        bitrev(&b2n(&bitrev(&x), t_br)),
        "transpose bridge"
    );

    // 4: the natural-order table yields maps that are NOT F composed with any
    // input (column) or output (row) permutation.
    for (name, m) in [
        ("b2n(T_nat)", matrix_of(&|x| b2n(x, t_nat))),
        ("n2b(T_nat)", matrix_of(&|x| n2b(x, t_nat))),
    ] {
        // column permutation: every column of M must be SOME column of F
        let col_perm_exists = (0..n).all(|j| {
            let col_m: Vec<_> = (0..n).map(|i| m[j][i]).collect();
            (0..n).any(|k| (0..n).all(|i| col_m[i] == f_matrix[i][k]))
        });
        // row permutation: every row of M must be SOME row of F
        let row_perm_exists = (0..n).all(|i| {
            let row_m: Vec<_> = (0..n).map(|j| m[j][i]).collect();
            (0..n).any(|k| (0..n).all(|j| row_m[j] == f_matrix[k][j]))
        });
        assert!(
            !col_perm_exists && !row_perm_exists,
            "{name} unexpectedly IS a permuted DFT"
        );
    }
    println!(
        "[ntt kernels] transposed pair confirmed; natural-order twiddles give a non-DFT map (n = {n})"
    );
}
