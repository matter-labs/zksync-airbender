//! Pins the CPU commit path's monomial LABELING, with no GPU involved.
//!
//! Runs the production `commit_trace_part` on a tiny hypercube column and
//! asserts coset 0's RS codeword equals naive evaluations under the NATURAL
//! labeling — coefficient `i` carries `x^i`, in natural domain order. That is
//! the authority the whole LSB track reads:
//! `lde_multiple_polys_parallel_from_hypercubes`
//! (prover/src/gkr/prover/stages/commitment_utils.rs:485-533, "natural
//! convention: variable b <-> exponent bit b") hands the Mobius output to
//! `compute_column_major_lde_from_monomial_form` (:190-231), whose parameter is
//! named `monomial_form_normal_order`. gpu_ntt's
//! `hypercube_monomials_are_natural_and_bitreversed_lde_relabels_them` pins the
//! GPU side of the same question.

use super::*;

#[test]
fn cpu_commit_path_labeling_is_natural() {
    use crate::upstream::commit_trace_part;
    use prover::field::Field;
    use prover::gkr::whir::ColumnMajorBaseOracleForLDE;

    let worker = Worker::new_with_num_threads(4);
    let log_n = 4usize;
    let n = 1usize << log_n;

    let evals: Vec<BF> = (0..n).map(|i| BF::new((7 + i * 5) as u32)).collect();

    // CPU reference: the Mobius transform, then naive evaluation both ways.
    let mut coeffs = evals.clone();
    prover::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs(
        &mut coeffs,
        log_n as u32,
    );
    let omega: BF = fft::domain_generator_for_size::<BF>(n as u64);
    let pow = |b: BF, e: usize| {
        let mut a = BF::ONE;
        for _ in 0..e {
            a.mul_assign(&b);
        }
        a
    };
    let br = |i: usize| {
        let mut r = 0usize;
        for b in 0..log_n {
            if i & (1 << b) != 0 {
                r |= 1 << (log_n - 1 - b);
            }
        }
        r
    };
    let mut nat = vec![BF::ZERO; n];
    let mut rev = vec![BF::ZERO; n];
    for j in 0..n {
        let x = pow(omega, j);
        for i in 0..n {
            let mut t = coeffs[i];
            t.mul_assign(&pow(x, i));
            nat[j].add_assign(&t);
            let mut u = coeffs[i];
            u.mul_assign(&pow(x, br(i)));
            rev[j].add_assign(&u);
        }
    }

    // Production CPU commit.
    let twiddles: fft::Twiddles<BF, std::alloc::Global> = fft::Twiddles::new(n, &worker);
    let inputs: Vec<&[BF]> = vec![&evals[..]];
    let oracle = commit_trace_part::<BF, BF, DefaultTreeConstructor, _>(
        &prover::gkr::prover::backend::NaiveBackend,
        &inputs,
        &twiddles,
        2, // lde_factor
        1, // whir_first_fold_step_log2 -> 2 values per leaf
        4, // tree cap size
        log_n,
        &worker,
    );
    let ColumnMajorBaseOracleForLDE::InMemory(ref in_mem) = oracle else {
        panic!("expected in-memory oracle");
    };
    let coset0 = &in_mem.cosets.cosets[0];
    let cpu_codeword: Vec<BF> = coset0.original_values_normal_order[0].column.to_vec();

    assert!(
        coset0.offset == BF::ONE,
        "coset 0 must be the unshifted domain",
    );
    assert!(
        nat != rev,
        "the fixture must distinguish the two labelings, or the pin below is vacuous",
    );
    assert!(
        cpu_codeword == nat,
        "the CPU commit path must evaluate coefficient i at exponent i; \
         bitreversed-labeling match instead: {}",
        cpu_codeword == rev,
    );
    let mut cw_rev = cpu_codeword.clone();
    fft::bitreverse_enumeration_inplace(&mut cw_rev);
    assert!(
        cw_rev != nat && cw_rev != rev,
        "the codeword is in natural domain order, so bitreversing it must match \
         neither labeling",
    );
}
