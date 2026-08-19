//! Pins the CPU commit path's monomial LABELING, with no GPU involved.
//!
//! Runs the production `commit_trace_part` on a tiny hypercube column and
//! compares coset 0's RS codeword against naive evaluations under both
//! exponent labelings. Read together with gpu_ntt's
//! `characterize_commit_chain_labeling_vs_cpu` (which pins the GPU side), this
//! says whether the two agree, differ by a permutation, or differ in value.

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
        2,      // lde_factor
        1,      // whir_first_fold_step_log2 -> 2 values per leaf
        4,      // tree cap size
        log_n,
        &worker,
    );
    let ColumnMajorBaseOracleForLDE::InMemory(ref in_mem) = oracle else {
        panic!("expected in-memory oracle");
    };
    let coset0 = &in_mem.cosets.cosets[0];
    let cpu_codeword: Vec<BF> = coset0.original_values_normal_order[0].column.to_vec();

    println!("coset0 offset == ONE: {}", coset0.offset == BF::ONE);
    println!("cpu_codeword == NATURAL-labeling: {}", cpu_codeword == nat);
    println!("cpu_codeword == BITREV-labeling:  {}", cpu_codeword == rev);
    let mut cw_rev = cpu_codeword.clone();
    fft::bitreverse_enumeration_inplace(&mut cw_rev);
    println!("bitrev(cpu_codeword) == NATURAL:  {}", cw_rev == nat);
    println!("bitrev(cpu_codeword) == BITREV:   {}", cw_rev == rev);
}
