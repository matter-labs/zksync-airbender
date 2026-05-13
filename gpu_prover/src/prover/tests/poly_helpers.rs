use super::*;

pub(super) fn compute_column_major_lde_from_monomial_form_for_test(
    monomial_coeffs: &[E4],
    twiddles: &Twiddles<BF, Global>,
    lde_factor: usize,
) -> Vec<(Box<[E4]>, BF)> {
    let trace_len_log2 = monomial_coeffs.len().trailing_zeros() as usize;
    let next_root = domain_generator_for_size::<BF>(((1 << trace_len_log2) * lde_factor) as u64);
    let root_powers =
        materialize_powers_serial_starting_with_one::<BF, Global>(next_root, lde_factor);
    let selected_twiddles = &twiddles.forward_twiddles[..(1 << (trace_len_log2 - 1))];

    (0..lde_factor)
        .map(|i| {
            let mut evals = monomial_coeffs.to_vec();
            let offset = root_powers[i];
            if i != 0 {
                fft::distribute_powers_serial(&mut evals[..], BF::ONE, offset);
            }
            bitreverse_enumeration_inplace(&mut evals[..]);
            fft::naive::serial_ct_ntt_bitreversed_to_natural(
                &mut evals[..],
                trace_len_log2 as u32,
                selected_twiddles,
            );
            (evals.into_boxed_slice(), offset)
        })
        .collect()
}

pub(super) fn compute_column_major_monomial_form_from_main_domain_owned_for_test(
    source_domain: Vec<E4>,
    twiddles: &Twiddles<BF, Global>,
) -> Vec<E4> {
    let trace_len_log2 = source_domain.len().trailing_zeros();
    let mut ifft = source_domain;
    let size_inv = BF::from_u32_unchecked(1 << trace_len_log2)
        .inverse()
        .unwrap();
    fft::naive::cache_friendly_ntt_natural_to_bitreversed(
        &mut ifft[..],
        trace_len_log2,
        &twiddles.inverse_twiddles[..],
    );
    for el in ifft.iter_mut() {
        el.mul_assign_by_base(&size_inv);
    }
    bitreverse_enumeration_inplace(&mut ifft[..]);

    ifft
}

pub(super) fn build_cpu_recursive_whir_oracle_for_test(
    monomial_coeffs: &[E4],
    twiddles: &Twiddles<BF, Global>,
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<BF, E4, DefaultTreeConstructor> {
    let cosets =
        compute_column_major_lde_from_monomial_form_for_test(monomial_coeffs, twiddles, lde_factor);
    let trace_len_log2 = monomial_coeffs.len().trailing_zeros() as usize;
    let mut wrapped_cosets = Vec::with_capacity(cosets.len());
    for (column, offset) in cosets.iter() {
        wrapped_cosets.push(ColumnMajorExtensionOracleForCoset {
            values_normal_order: ColumnMajorCosetBoundTracePart {
                column: column.clone().into(),
                offset: *offset,
            },
        });
    }
    let source: Vec<_> = wrapped_cosets
        .iter()
        .map(|coset| vec![&coset.values_normal_order.column[..]])
        .collect();
    let source_ref: Vec<_> = source.iter().map(|entry| &entry[..]).collect();
    let tree =
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::construct_from_cosets::<
            E4,
            Global,
        >(
            &source_ref,
            values_per_leaf,
            tree_cap_size,
            true,
            true,
            false,
            worker,
        );

    ColumnMajorExtensionOracleForLDE {
        cosets: wrapped_cosets,
        tree,
        values_per_leaf,
        trace_len_log2,
    }
}

pub(super) fn fold_monomial_form_for_test(input: &mut Vec<E4>, challenge: E4) {
    assert!(input.len().is_power_of_two());
    let mut buffer = Vec::with_capacity(input.len() / 2);
    for [c0, c1] in input.as_chunks::<2>().0.iter() {
        let mut result = *c1;
        result.mul_assign(&challenge);
        result.add_assign(c0);
        buffer.push(result);
    }
    *input = buffer;
}

pub(super) fn fold_evaluation_form_for_test(input: &mut Vec<E4>, challenge: E4) {
    assert!(input.len().is_power_of_two());
    let half_len = input.len() / 2;
    let (first_half, second_half) = input.split_at_mut(half_len);
    for (a, b) in first_half.iter_mut().zip(second_half.iter()) {
        let mut t = *b;
        t.sub_assign(a);
        t.mul_assign(&challenge);
        a.add_assign(&t);
    }
    input.truncate(half_len);
}

pub(super) fn fold_eq_poly_for_test(eq_poly: &mut Vec<E4>, challenge: E4) {
    fold_evaluation_form_for_test(eq_poly, challenge);
}

pub(super) fn special_three_point_eval_for_test(a: &[E4], b: &[E4]) -> (E4, E4, E4) {
    assert_eq!(a.len(), b.len());
    let half = a.len() / 2;
    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    let (a_low, a_high) = a.split_at(half);
    let (b_low, b_high) = b.split_at(half);
    let mut f0 = E4::ZERO;
    let mut f1 = E4::ZERO;
    let mut f_half = E4::ZERO;
    for ((a0, a1), (b0, b1)) in a_low
        .iter()
        .zip(a_high.iter())
        .zip(b_low.iter().zip(b_high.iter()))
    {
        let mut t0 = *a0;
        t0.mul_assign(b0);
        f0.add_assign(&t0);

        let mut t1 = *a1;
        t1.mul_assign(b1);
        f1.add_assign(&t1);

        let mut t_half = *a0;
        t_half.add_assign(a1);
        let mut eq_half = *b0;
        eq_half.add_assign(b1);
        t_half.mul_assign(&eq_half);
        f_half.add_assign(&t_half);
    }
    f_half.mul_assign_by_base(&quart);
    (f0, f1, f_half)
}

pub(super) fn special_lagrange_interpolate_for_test(
    eval_at_0: E4,
    eval_at_1: E4,
    eval_at_random: E4,
    random_point: E4,
) -> [E4; 3] {
    let mut coeffs_for_0 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_0[1] = E4::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();
    coeffs_for_0[0] = random_point;

    let mut coeffs_for_1 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_1[1] = random_point;
    coeffs_for_1[1].negate();

    let mut coeffs_for_random = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_random[1] = E4::ONE;
    coeffs_for_random[1].negate();

    let mut dens = [E4::ONE, E4::ONE, E4::ONE];
    let mut t = E4::ZERO;
    t.sub_assign(&E4::ONE);
    dens[0].mul_assign(&t);
    let mut t = E4::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E4::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let t = random_point;
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E4::ONE);
    dens[2].mul_assign(&t);

    let mut buffer = [E4::ZERO; 3];
    batch_inverse_inplace(&mut dens, &mut buffer);

    let mut result = [E4::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random),
    ] {
        for (dst, coeff) in result.iter_mut().zip(coeffs.into_iter()) {
            let mut term = coeff;
            term.mul_assign(&den);
            term.mul_assign(&eval);
            dst.add_assign(&term);
        }
    }

    result
}

pub(super) fn make_pows_for_test(mut el: E4, num_powers: usize) -> Vec<E4> {
    let mut result = Vec::with_capacity(num_powers);
    for _ in 0..num_powers {
        result.push(el);
        el.square();
    }
    result
}

pub(super) fn update_eq_poly_for_test(
    eq_poly: &mut [E4],
    ood_samples: &[(E4, E4)],
    in_domain_samples: &[(BF, E4)],
) {
    for (point, challenge) in ood_samples.iter() {
        let pows = make_pows_for_test(*point, eq_poly.len().trailing_zeros() as usize);
        let eqs = make_eq_poly_in_full::<E4>(&pows, &Worker::new());
        for (dst, src) in eq_poly.iter_mut().zip(eqs.last().unwrap().iter()) {
            let mut t = *challenge;
            t.mul_assign(src);
            dst.add_assign(&t);
        }
    }
    for (point, challenge) in in_domain_samples.iter() {
        let pows = make_pows_for_test(
            E4::from_base(*point),
            eq_poly.len().trailing_zeros() as usize,
        );
        let eqs = make_eq_poly_in_full::<E4>(&pows, &Worker::new());
        for (dst, src) in eq_poly.iter_mut().zip(eqs.last().unwrap().iter()) {
            let mut t = *challenge;
            t.mul_assign(src);
            dst.add_assign(&t);
        }
    }
}

pub(super) fn evaluate_monomial_form_for_test(coeffs: &[E4], point: E4) -> E4 {
    let mut result = E4::ZERO;
    let mut current = E4::ONE;
    for coeff in coeffs.iter() {
        let mut term = *coeff;
        term.mul_assign(&current);
        result.add_assign(&term);
        current.mul_assign(&point);
    }
    result
}

pub(super) fn fold_coset_for_test(
    mut flattened_evals: Vec<E4>,
    num_folding_rounds: usize,
    folding_challenges: &[E4],
    base_root_inv: &BF,
    high_powers_offsets: &[BF],
    two_inv: &BF,
) -> E4 {
    let mut root_inv = *base_root_inv;
    let mut buffer = Vec::with_capacity(flattened_evals.len());
    for folding_step in 0..num_folding_rounds {
        let (src, dst) = if folding_step % 2 == 0 {
            (&flattened_evals[..], &mut buffer)
        } else {
            (&buffer[..], &mut flattened_evals)
        };
        dst.clear();
        for (set_idx, [a, b]) in src.as_chunks::<2>().0.iter().enumerate() {
            let mut t = *a;
            t.sub_assign(b);
            t.mul_assign(&folding_challenges[folding_step]);
            let mut root = root_inv;
            root.mul_assign(&high_powers_offsets[set_idx]);
            t.mul_assign_by_base(&root);
            t.add_assign(a);
            t.add_assign(b);
            t.mul_assign_by_base(two_inv);
            dst.push(t);
        }
        root_inv.square();
    }
    if num_folding_rounds % 2 == 1 {
        buffer[0]
    } else {
        flattened_evals[0]
    }
}
