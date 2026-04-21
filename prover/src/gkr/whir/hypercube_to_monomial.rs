use super::*;

pub fn multivariate_coeffs_into_hypercube_evals<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1 << size_log2);

    // e.g. we have a poly over X1 and X2 of c0 + c1 X1 + c2 X2 + c3 X1X2
    // and want to compute evaluations at (0, 0), (1, 0), (0, 1), and (1, 1) (and output in this order, so X1 is most-signinicant digit in enumeration)
    // Coefficient at index [i] is one for the term where coefficient in front of X1 is get_bit(i, 0), coefficient for X2 is get_bit(i, 1) and so on.
    // This naturally corresponds to the mapping into univariate poly if X1 = X, X2 = X^2 and so on - then index [i] is just a coefficient for X^i

    // Evaluation procedure is very much like FFT - it's recursive, but out evaluation basis is not polynomial, even though highly structured.
    // E.g. let's look at evaluations for some fixed X2, and for X1 = 0 and 1
    // f(0, X2) = c0 + c1 * 0 + c2 * X2 + c3 * 0 * X2
    // f(1, X2) = c0 + c1 * 1 + c2 * X2 + c3 * 1 * X2
    // That differ only in the value that have bit(i, 0) == 1. So, what we do, is we "fix" some bit, and for all remaining pairs
    // compute either their value, or value + value of opposite bit

    // Self-check
    // f(0, 0) = c0
    // f(0, 1) = c0 + c2
    // f(1, 0) = c0 + c1
    // f(1, 1) = c0 + c1 + c2 + c3

    // we start with the vector of c0, c1, c2, c3
    // "fix" the bit 0 - so our pairs are (c0, c1) and (c2, c3)
    // new evaluations are (c0, c0 + c1), (c2, c2 + c3)
    // then we "fix" bit 1 - new pairs are (c0, c2) and (c0 + c1, c2 + c3) (but we do not rearrange the array and just use stride)
    // and so we get c0, c0 + c1, c0 + c2, c0 + c1 + c2 + c3  - exactly the values, where x1-corresponding "bit" is the lowest one in the index

    // Inverse transformation requires to compute pairs as a' = a, b' = b - a instead, but starting from the MSB (largest stride)

    // first round for simplicity
    for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
        b.add_assign(&a);
    }

    let mut stride = 2;
    let mut iterations = 2;
    let len = 1 << size_log2;
    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].add_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride *= 2;
        iterations *= 2;
    }
}

pub fn multivariate_hypercube_evals_into_coeffs<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1 << size_log2);
    let len = 1 << size_log2;

    let mut stride = len / 2;
    let mut iterations = len / 2;

    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].sub_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride /= 2;
        iterations /= 2;
    }

    for [a, b] in input.as_chunks_mut::<2>().0.iter_mut() {
        b.sub_assign(&a);
    }
}

#[cfg(test)]
mod test {
    use field::baby_bear::base::BabyBearField;

    use super::*;

    type F = BabyBearField;

    #[test]
    fn test_forward() {
        let size: usize = 4;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        assert_eq!(coeffs[0], F::ZERO); // x1 = 0, x2 = 0, c0
        assert_eq!(coeffs[1], F::ONE); // x1 = 1, x2 = 0, c0 + c1
        assert_eq!(coeffs[2], F::from_u32_unchecked(2)); // x1 = 0, x2 = 1, c0 + c2
        assert_eq!(coeffs[3], F::from_u32_unchecked(1 + 2 + 3)); // x1 = 1, x2 = 1, c0 + c1 + c2 + c3
    }

    #[test]
    fn test_forward_8() {
        let size: usize = 8;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        // as x3 is 0, we should have the same values as in the test above
        assert_eq!(coeffs[0], F::ZERO); // x1 = 0, x2 = 0, x3 = 0, c0
        assert_eq!(coeffs[1], F::ONE); // x1 = 1, x2 = 0, x3 = 0, c0 + c1
        assert_eq!(coeffs[2], F::from_u32_unchecked(2)); // x1 = 0, x2 = 1, x3 = 0, c0 + c2
        assert_eq!(coeffs[3], F::from_u32_unchecked(1 + 2 + 3)); // x1 = 1, x2 = 1, x3 = 0, c0 + c1 + c2 + c3
                                                                 // and only here we start to get contributions due to x3
        assert_eq!(coeffs[4], F::from_u32_unchecked(4)); // x1 = 0, x2 = 0, x3 = 1, c0 + c4
        assert_eq!(coeffs[5], F::from_u32_unchecked(1 + 4 + 5)); // x1 = 1, x2 = 0, x3 = 1, c0 + c1 + c4 + c5
        assert_eq!(coeffs[6], F::from_u32_unchecked(2 + 4 + 6)); // x1 = 0, x2 = 1, x3 = 1, c0 + c2 + c4 + c6
        assert_eq!(coeffs[7], F::from_u32_unchecked(1 + 2 + 3 + 4 + 5 + 6 + 7));
        // x1 = 1, x2 = 1, x3 = 1, all
    }

    #[test]
    fn test_roundtrip() {
        let size: usize = 8;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        let reference = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        multivariate_hypercube_evals_into_coeffs(&mut coeffs, size.trailing_zeros());
        assert_eq!(coeffs, reference);
    }

    #[test]
    fn test_roundtrip_large() {
        let size: usize = 1 << 20;
        let mut coeffs: Vec<F> = (0..size)
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();
        let reference = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut coeffs, size.trailing_zeros());
        multivariate_hypercube_evals_into_coeffs(&mut coeffs, size.trailing_zeros());
        assert_eq!(coeffs, reference);
    }
}
