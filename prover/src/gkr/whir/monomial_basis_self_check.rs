// if instead of 0/1 we use a hypercube basis 0/infinity, then for RS code word evaluation our monomial form numerically
// coincides with trace values. We do a short self-check here

// - Lagrange poly is eq(x, y) = 1 + xy
// - RS definition from WHIR is eval(omega) = \sum_x eq(x, powers(omega)) p(x)
// - RS evaluation is just an FFT

use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

use super::*;

type F = BabyBearField;
type E = BabyBearExt4;

fn evaluate_at_base_point_for_zero_infinity_basis<F: PrimeField, E: FieldExtension<F> + Field>(
    evals: &[E],
    point: &[F],
) -> E {
    let mut eqs = make_eq_poly_for_zero_infinity_basis_impl::<F, F, true>(point);
    let eq = eqs.pop().unwrap();
    assert_eq!(eq.len(), evals.len());
    let mut result = E::ZERO;
    for (a, b) in eq.iter().zip(evals.iter()) {
        let mut t = *b;
        t.mul_assign_by_base(a);
        result.add_assign(&t);
    }
    result
}

fn make_eq_poly_for_zero_infinity_basis_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const FULL: bool,
>(
    coordinates: &[E],
) -> Vec<Box<[E]>> {
    // poly is 1 + xy formally, but it's 1 at 0, and y at infinity

    assert!(coordinates.len() > 0);
    // challenges[0] is the challenge used to fold a variable, that is encoded as MSB in the values enumeration,
    // and we will produce the outputs in a same form. We also keep all intermediate forms for simplicity
    let mut result = Vec::with_capacity(coordinates.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let mut size = 1;
    let mut idx = coordinates.len();

    let bound = if FULL {
        coordinates.len() + 1
    } else {
        coordinates.len()
    };

    for _ in 1..bound {
        size *= 2;
        idx -= 1;

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");

        let coordinate = coordinates[idx];

        let eq_at_zero = E::ONE;

        let eq_at_infinity = coordinate;

        let half_size = size / 2;

        assert_eq!(previous_layer.len(), half_size);

        for index in 0..half_size {
            let mut left = previous_layer[index];
            let mut right = left;
            left.mul_assign(&eq_at_zero);
            right.mul_assign(&eq_at_infinity);
            layer[index].write(left);
            layer[index + half_size].write(right);
        }

        let layer = unsafe { layer.assume_init() };
        result.push(layer);
    }

    result
}

fn make_eq_poly_for_zero_infinity_basis_evaluated_at_zero_one_impl<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const FULL: bool,
>(
    coordinates: &[E],
) -> Vec<Box<[E]>> {
    // poly is 1 + xy, it's 1 at 0, and 1 + y at 1

    assert!(coordinates.len() > 0);
    // challenges[0] is the challenge used to fold a variable, that is encoded as MSB in the values enumeration,
    // and we will produce the outputs in a same form. We also keep all intermediate forms for simplicity
    let mut result = Vec::with_capacity(coordinates.len() + 1);
    result.push(vec![E::ONE].into_boxed_slice());

    let mut size = 1;
    let mut idx = coordinates.len();

    let bound = if FULL {
        coordinates.len() + 1
    } else {
        coordinates.len()
    };

    for _ in 1..bound {
        size *= 2;
        idx -= 1;

        let mut layer = Box::new_uninit_slice(size);
        let previous_layer = result.last().expect("is present");

        let coordinate = coordinates[idx];

        let eq_at_zero = E::ONE;

        let mut eq_at_one = coordinate;
        eq_at_one.add_assign(&E::ONE);

        let half_size = size / 2;

        assert_eq!(previous_layer.len(), half_size);

        for index in 0..half_size {
            let mut left = previous_layer[index];
            let mut right = left;
            left.mul_assign(&eq_at_zero);
            right.mul_assign(&eq_at_one);
            layer[index].write(left);
            layer[index + half_size].write(right);
        }

        let layer = unsafe { layer.assume_init() };
        result.push(layer);
    }

    result
}

#[test]
fn quick_self_test() {
    let domain_size = 4usize;
    let worker = Worker::new_with_num_threads(1);

    let mut monomial_form: Vec<_> = (0..domain_size)
        .map(|el| F::from_nonreduced_u32(el as u32))
        .collect();
    let twiddles = Twiddles::<F, Global>::new(domain_size, &worker);

    let mut rs_code_word = monomial_form.clone();
    bitreverse_enumeration_inplace(&mut rs_code_word);
    fft::naive::serial_ct_ntt_bitreversed_to_natural(
        &mut rs_code_word[..],
        domain_size.trailing_zeros(),
        &twiddles.forward_twiddles,
    );

    let generator = domain_generator_for_size::<F>(domain_size as u64);
    bitreverse_enumeration_inplace(&mut monomial_form);
    for i in 0..domain_size {
        let omega = generator.pow(i as u32);
        let pows = make_pows(omega, domain_size.trailing_zeros() as usize);
        let domain: Vec<BabyBearField, Global> =
            materialize_powers_serial_starting_with_one(omega, domain_size as usize);
        let eval_from_multivariate =
            evaluate_at_base_point_for_zero_infinity_basis(&monomial_form, &pows);

        assert_eq!(rs_code_word[i], eval_from_multivariate);
    }
}

#[test]
fn quick_test_binding_poly_and_sumcheck() {
    let size = 8usize;

    let num_vars = size.trailing_zeros() as usize;
    let challenge_coordiantes: Vec<_> = (1..=num_vars)
        .map(|el| F::from_nonreduced_u32((el * 10) as u32))
        .collect();
    // let challenge_coordiantes: Vec<_> = (1..=num_vars)
    //     .map(|el| F::from_nonreduced_u32(1 as u32))
    //     .collect();
    let mut eqs_at_zero_inf =
        make_eq_poly_for_zero_infinity_basis_impl::<F, F, true>(&challenge_coordiantes);

    let a: Vec<_> = (1..=size)
        .map(|el| F::from_nonreduced_u32(el as u32))
        .collect();

    let b: Vec<_> = (1..=size)
        .map(|el| F::from_nonreduced_u32((el * 1000) as u32))
        .collect();

    let output: Vec<_> = a
        .iter()
        .zip(b.iter())
        .map(|(a, b)| {
            let mut t = *a;
            t.mul_assign(&b);

            t
        })
        .collect();

    dbg!(&a);
    dbg!(&b);
    dbg!(&output);
    dbg!(&eqs_at_zero_inf);

    // there are multiple ways to "save" on computations in sumcheck of the special form
    // like we have - \sum_x eq(x, r) * a(x) * b(x), and below we will split it as G(X) = \sum_x eq(X, r0) * eq(x, r1, ...) * A(X, x) * B(X, x)

    // We always have the following constraints to consider
    // claim = G(0) + G(inf)
    // eq(X, r0) == 1 + r0 * X

    // and in general G(X) = (r0 * X + 1) * (c * X^2 + d * X + e)
    // where quadratic part comes from the A(X) * B(X)

    // note that G(0) and G(infinity) are nice to compute in initial rounds as they are
    // just exactly the output values of the GKR layer
    // So we choose to compute G(0) and get
    // G(0) == `e`
    // claim - G(0) = G(infinity) = r0 * `c`
    // and the only thing we need to identify now is `d`,
    // so we need one more evaluation and we can pick any evaluation point and it's natural to do G(1)

    // NOTE: we will need to be more careful when we mix linear and quadratic terms in the batched sumcheck

    // Alternative is to define a sumcheck in different "coordinates" than default representation itself.
    // So we will say that
    // claim = G(0) + G(1) = e + (r0 + 1) * (c + d + e),
    // and prover will compute G(0) (because it's nice to compute), getting
    // `e` and then we get G(1) = (r0 + 1) * (c + d + e),
    // and then compute G(infinity) as it's also nice to compute, getting `c`, so we have enough points
    // to get all the values. But such aproach only works for the first round,
    // so we will have output(r) = claim = \sum_{x_0 = {0, 1}, x_{1,...} = {0, inf}^{N-1}} eq_{0/1}(x, r0) * eq_{0/inf}(x1, ..., r1, ...) * a(x) * b(x)

    // Here we self-check our second approach

    let eq_table_at_zero_inf = eqs_at_zero_inf.last().unwrap();
    let mut claim = F::ZERO;
    let mut g_0_self_check = F::ZERO;
    for i in 0..size / 2 {
        let a_at_0 = a[i];
        let b_at_0 = b[i];
        let a_at_inf = a[i + size / 2];
        let b_at_inf = b[i + size / 2];

        let naive_out_at_0 = output[i];
        let mut a_at_1 = a_at_inf;
        a_at_1.add_assign(&a_at_0);
        let mut b_at_1 = b_at_inf;
        b_at_1.add_assign(&b_at_0);

        let mut out_at_0 = a_at_0;
        out_at_0.mul_assign(&b_at_0);
        let mut out_at_1 = a_at_1;
        out_at_1.mul_assign(&b_at_1);

        assert_eq!(naive_out_at_0, out_at_0);

        let eq_at_0 = eq_table_at_zero_inf[i];
        let eq_at_inf = eq_table_at_zero_inf[i + size / 2];
        let mut eq_at_1 = eq_at_0;
        eq_at_1.add_assign(&eq_at_inf);

        out_at_0.mul_assign(&eq_at_0);
        out_at_1.mul_assign(&eq_at_1);

        claim.add_assign(&out_at_0);
        claim.add_assign(&out_at_1);

        g_0_self_check.add_assign(&out_at_0);
    }

    // now we actually do the sumcheck, and we will only do one round for our self-check
    let mut g_at_0 = F::ZERO;
    for i in 0..size / 2 {
        let a_at_0 = a[i];
        let b_at_0 = b[i];
        let mut out_at_0 = output[i];

        {
            let mut t = a_at_0;
            t.mul_assign(&b_at_0);
            assert_eq!(t, out_at_0);
        }
        out_at_0.mul_assign(&eq_table_at_zero_inf[i]);

        g_at_0.add_assign(&out_at_0);
    }
    assert_eq!(g_0_self_check, g_at_0);

    let mut g_at_inf = F::ZERO;
    for i in 0..size / 2 {
        let a_at_inf = a[i + size / 2];
        let b_at_inf = b[i + size / 2];
        let mut out_at_inf = output[i + size / 2];

        {
            let mut t = a_at_inf;
            t.mul_assign(&b_at_inf);
            assert_eq!(t, out_at_inf);
        }
        out_at_inf.mul_assign(&eq_table_at_zero_inf[i + size / 2]);

        g_at_inf.add_assign(&out_at_inf);
    }

    let mut g_at_1 = claim;
    g_at_1.sub_assign(&g_at_0);

    // now we get the coefficients

    // lowest
    let e = g_at_0;

    // highest
    let mut c = g_at_inf;
    c.mul_assign(&challenge_coordiantes[0].inverse().unwrap());

    let mut t = challenge_coordiantes[0];
    t.add_assign(&F::ONE);
    let mut d = g_at_1;
    d.mul_assign(&t.inverse().unwrap());
    d.sub_assign(&e);
    d.sub_assign(&c);

    // self-check
    let mut coeffs = vec![];
    coeffs.push(e);
    let mut t = e;
    t.mul_assign(&challenge_coordiantes[0]);
    t.add_assign(&d);
    coeffs.push(t);
    let mut t = d;
    t.mul_assign(&challenge_coordiantes[0]);
    t.add_assign(&c);
    coeffs.push(t);
    let mut t = c;
    t.mul_assign(&challenge_coordiantes[0]);
    assert_eq!(t, g_at_inf);
    coeffs.push(t);

    dbg!(&coeffs);

    let g_at_0_reevaluated = evaluate_monomial_form_serial(&coeffs, &F::ZERO);
    assert_eq!(g_at_0_reevaluated, g_at_0);
    let g_at_1_reevaluated = evaluate_monomial_form_serial(&coeffs, &F::ONE);
    assert_eq!(g_at_1_reevaluated, g_at_1);

    let challenge = F::from_nonreduced_u32(100);

    let new_claim = evaluate_monomial_form_serial(&coeffs, &challenge);
    dbg!(new_claim);

    // now we do the binding (fold), and check it again
    let mut new_a = a[..size / 2].to_vec();
    let mut new_b = b[..size / 2].to_vec();
    for (dst, src) in new_a.iter_mut().zip(a[size / 2..].iter()) {
        let mut t = challenge;
        t.mul_assign(src);
        dst.add_assign(&t);
    }
    for (dst, src) in new_b.iter_mut().zip(b[size / 2..].iter()) {
        let mut t = challenge;
        t.mul_assign(src);
        dst.add_assign(&t);
    }

    dbg!(&new_a);
    dbg!(&new_b);

    // we should bind equality poly, but we have evaluation table for eq(coordiantes except first)
    // already, and eq(X, challenge_coordiantes[0]) at new_challenge is just 1 + new_challenge * challenge_coordiantes[0]

    let mut t0 = challenge_coordiantes[0];
    t0.mul_assign(&challenge);
    t0.add_assign(&F::ONE);

    let extended_eq = eqs_at_zero_inf.pop().unwrap();
    let mut new_eq = extended_eq[..size / 2].to_vec();
    for (dst, src) in new_eq.iter_mut().zip(extended_eq[size / 2..].iter()) {
        let mut t = challenge;
        t.mul_assign(src);
        dst.add_assign(&t);
    }

    dbg!(&new_eq);

    let eq_table_at_zero_inf = eqs_at_zero_inf.last().unwrap();
    assert_eq!(eq_table_at_zero_inf.len(), new_a.len());

    let mut naive_eval = F::ZERO;
    for i in 0..new_a.len() / 2 {
        let a_at_0 = new_a[i];
        let b_at_0 = new_b[i];
        let a_at_inf = new_a[i + new_a.len() / 2];
        let b_at_inf = new_b[i + new_a.len() / 2];

        let mut out_at_0 = a_at_0;
        out_at_0.mul_assign(&b_at_0);
        let mut out_at_inf = a_at_inf;
        out_at_inf.mul_assign(&b_at_inf);

        let mut eq_at_0 = eq_table_at_zero_inf[i];
        let mut eq_at_inf = eq_table_at_zero_inf[i + new_a.len() / 2];
        eq_at_0.mul_assign(&t0);
        eq_at_inf.mul_assign(&t0);

        assert_eq!(eq_at_0, new_eq[i]);
        assert_eq!(eq_at_inf, new_eq[i + new_a.len() / 2]);

        out_at_0.mul_assign(&eq_at_0);
        out_at_inf.mul_assign(&eq_at_inf);

        naive_eval.add_assign(&out_at_0);
        naive_eval.add_assign(&out_at_inf);
    }

    assert_eq!(naive_eval, new_claim);

    // and we can fold once again, and check.
    // Now new_claim = G(0) + G(inf)

    // now we actually do the sumcheck, and we will only do one round for our self-check
    let mut g_at_0 = F::ZERO;
    for i in 0..new_a.len() / 2 {
        let a_at_0 = new_a[i];
        let b_at_0 = new_b[i];

        let mut out_at_0 = a_at_0;
        out_at_0.mul_assign(&b_at_0);

        let mut eq_at_0 = eq_table_at_zero_inf[i];
        eq_at_0.mul_assign(&t0);

        out_at_0.mul_assign(&eq_at_0);

        g_at_0.add_assign(&out_at_0);
    }

    let mut g_at_inf = new_claim;
    g_at_inf.sub_assign(&g_at_0);

    // and prover anyway needs to compute g(1)
    let mut g_at_1 = F::ZERO;
    for i in 0..new_a.len() / 2 {
        let a_at_0 = new_a[i];
        let b_at_0 = new_b[i];
        let a_at_inf = new_a[i + new_a.len() / 2];
        let b_at_inf = new_b[i + new_a.len() / 2];

        let mut a_at_1 = a_at_inf;
        a_at_1.add_assign(&a_at_0);
        let mut b_at_1 = b_at_inf;
        b_at_1.add_assign(&b_at_0);

        let mut out_at_1 = a_at_1;
        out_at_1.mul_assign(&b_at_1);

        let mut eq_at_0 = eq_table_at_zero_inf[i];
        let mut eq_at_inf = eq_table_at_zero_inf[i + new_a.len() / 2];
        eq_at_0.mul_assign(&t0);
        eq_at_inf.mul_assign(&t0);

        let mut eq_at_1 = eq_at_0;
        eq_at_1.add_assign(&eq_at_inf);

        out_at_1.mul_assign(&eq_at_1);

        g_at_1.add_assign(&out_at_1);
    }

    // same way as before we interpolate
    // lowest
    let e = g_at_0;

    // highest
    let mut c = g_at_inf;
    c.mul_assign(&challenge_coordiantes[1].inverse().unwrap());

    let mut t = challenge_coordiantes[1];
    t.add_assign(&F::ONE);
    let mut d = g_at_1;
    d.mul_assign(&t.inverse().unwrap());
    d.sub_assign(&e);
    d.sub_assign(&c);

    // self-check
    let mut coeffs = vec![];
    coeffs.push(e);
    let mut t = e;
    t.mul_assign(&challenge_coordiantes[1]);
    t.add_assign(&d);
    coeffs.push(t);
    let mut t = d;
    t.mul_assign(&challenge_coordiantes[1]);
    t.add_assign(&c);
    coeffs.push(t);
    let mut t = c;
    t.mul_assign(&challenge_coordiantes[1]);
    assert_eq!(t, g_at_inf);
    coeffs.push(t);

    dbg!(&coeffs);

    let g_at_0_reevaluated = evaluate_monomial_form_serial(&coeffs, &F::ZERO);
    assert_eq!(g_at_0_reevaluated, g_at_0);
    let g_at_1_reevaluated = evaluate_monomial_form_serial(&coeffs, &F::ONE);
    assert_eq!(g_at_1_reevaluated, g_at_1);

    let challenge = F::from_nonreduced_u32(1000);

    let new_claim = evaluate_monomial_form_serial(&coeffs, &challenge);
    dbg!(new_claim);

    // and final self-verification
    let mut new_new_a = new_a[..new_a.len() / 2].to_vec();
    let mut new_new_b = new_b[..new_a.len() / 2].to_vec();
    for (dst, src) in new_new_a.iter_mut().zip(new_a[new_a.len() / 2..].iter()) {
        let mut t = challenge;
        t.mul_assign(src);
        dst.add_assign(&t);
    }
    for (dst, src) in new_new_b.iter_mut().zip(new_b[new_a.len() / 2..].iter()) {
        let mut t = challenge;
        t.mul_assign(src);
        dst.add_assign(&t);
    }

    dbg!(&new_new_a);
    dbg!(&new_new_b);

    let mut t1 = challenge_coordiantes[1];
    t1.mul_assign(&challenge);
    t1.add_assign(&F::ONE);

    let mut new_new_eq = new_eq[..new_eq.len() / 2].to_vec();
    for (dst, src) in new_new_eq.iter_mut().zip(new_eq[new_eq.len() / 2..].iter()) {
        let mut t = challenge;
        t.mul_assign(src);
        dst.add_assign(&t);
    }

    dbg!(&new_eq);

    let _ = eqs_at_zero_inf.pop().unwrap();
    let eq_table_at_zero_inf = eqs_at_zero_inf.last().unwrap();
    assert_eq!(eq_table_at_zero_inf.len(), new_new_a.len());

    let mut naive_eval = F::ZERO;
    for i in 0..new_new_a.len() / 2 {
        let a_at_0 = new_new_a[i];
        let b_at_0 = new_new_b[i];
        let a_at_inf = new_new_a[i + new_new_a.len() / 2];
        let b_at_inf = new_new_b[i + new_new_a.len() / 2];

        let mut out_at_0 = a_at_0;
        out_at_0.mul_assign(&b_at_0);
        let mut out_at_inf = a_at_inf;
        out_at_inf.mul_assign(&b_at_inf);

        let mut eq_at_0 = eq_table_at_zero_inf[i];
        let mut eq_at_inf = eq_table_at_zero_inf[i + new_new_a.len() / 2];
        eq_at_0.mul_assign(&t0);
        eq_at_0.mul_assign(&t1);
        eq_at_inf.mul_assign(&t0);
        eq_at_inf.mul_assign(&t1);

        assert_eq!(eq_at_0, new_new_eq[i]);
        assert_eq!(eq_at_inf, new_new_eq[i + new_new_a.len() / 2]);

        out_at_0.mul_assign(&eq_at_0);
        out_at_inf.mul_assign(&eq_at_inf);

        naive_eval.add_assign(&out_at_0);
        naive_eval.add_assign(&out_at_inf);
    }

    assert_eq!(naive_eval, new_claim);
}

/// LSB-consistency baseline for the natural-order (variable b <-> exponent
/// bit b) convention: commitment (coeffs + RS codeword WITHOUT either
/// bitreverse), at-point evaluation, an identity (copy-gate) sumcheck through
/// the converted LSB kernels with the monomial track folded in lockstep, and
/// one WHIR-style codeword fold -- each stage asserted against the previous.
#[test]
fn quick_lsb_consistency_chain() {
    use crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first;
    let worker = Worker::new_with_num_threads(1);
    let size = 8usize;
    let num_vars = size.trailing_zeros() as usize;
    let lde_factor = 2usize;
    let domain_size = size * lde_factor;

    // hypercube evals in natural order: index bit b <-> variable b
    let evals: Vec<F> = (0..size)
        .map(|el| F::from_nonreduced_u32((el * el + 3 * el + 7) as u32))
        .collect();

    // ---- commitment side ----
    // multilinear-natural monomial form: NO bitreverse before the transform
    let mut coeffs = evals.clone();
    crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs(
        &mut coeffs,
        num_vars as u32,
    );
    // round-trip sanity
    {
        let mut back = coeffs.clone();
        multivariate_coeffs_into_hypercube_evals(&mut back, num_vars as u32);
        assert_eq!(back, evals, "zeta round trip");
    }
    // RS codeword over the LDE domain: the multilinear-natural coefficient
    // order IS the bitreversed univariate order the bitreversed->natural NTT
    // consumes, so NO explicit bitreverse happens here either. The encoded
    // univariate is P(X) = sum_m c_m X^int(m) with exponent bit b = variable
    // b (int(m) = m since the array is in natural multilinear order).
    let twiddles = Twiddles::<F, Global>::new(domain_size, &worker);
    let mut rs_code_word = vec![F::ZERO; domain_size];
    rs_code_word[..size].copy_from_slice(&coeffs);
    // zero-padded univariate coeffs in natural order -> bitreverse the FULL
    // padded vector to feed the bitreversed->natural NTT
    bitreverse_enumeration_inplace(&mut rs_code_word);
    fft::naive::serial_ct_ntt_bitreversed_to_natural(
        &mut rs_code_word[..],
        domain_size.trailing_zeros(),
        &twiddles.forward_twiddles,
    );
    // consistency: codeword[i] == multilinear at (w^i, w^2i, w^4i) with the
    // NATURAL eq read (bit b <-> pows[b]), for every domain point
    let generator = domain_generator_for_size::<F>(domain_size as u64);
    for i in 0..domain_size {
        let omega_i = generator.pow(i as u32);
        let pows = make_pows(omega_i, num_vars);
        let eq = make_eq_table_lsb_first::<F>(&pows, &worker);
        let mut eval_from_multilinear = F::ZERO;
        for (e, w) in evals.iter().zip(eq.iter()) {
            let mut t = *e;
            t.mul_assign(w);
            eval_from_multilinear.add_assign(&t);
        }
        assert_eq!(
            rs_code_word[i], eval_from_multilinear,
            "codeword vs powers-eq multilinear at domain index {i}"
        );
    }

    // ---- eval-storing oracle loop: main-domain encode -> inverse == coeffs ----
    {
        let trace_twiddles = Twiddles::<F, Global>::new(size, &worker);
        // main-domain values = P_new(w8^k): natural coeffs -> bitreverse -> NTT
        let mut main_vals = coeffs.clone();
        bitreverse_enumeration_inplace(&mut main_vals);
        fft::naive::serial_ct_ntt_bitreversed_to_natural(
            &mut main_vals[..],
            size.trailing_zeros(),
            &trace_twiddles.forward_twiddles,
        );
        let recovered = crate::gkr::prover::backend::test_helpers_monomial_from_main_domain::<F>(
            main_vals.clone(),
            &trace_twiddles,
            &worker,
        );
        assert_eq!(recovered, coeffs, "main-domain inverse round trip");
    }

    // ---- at-point claim + identity (copy-gate) sumcheck ----
    let point: Vec<E> = (0..num_vars)
        .map(|b| {
            let mut v = E::from_base(F::from_nonreduced_u32((17 * b + 5) as u32));
            v.mul_assign(&E::from_base(F::from_nonreduced_u32(1000)));
            v
        })
        .collect();
    let eq_full = make_eq_table_lsb_first::<E>(&point, &worker);
    let mut claim = E::ZERO;
    for (e, w) in evals.iter().zip(eq_full.iter()) {
        let mut t = *w;
        t.mul_assign_by_base(e);
        claim.add_assign(&t);
    }

    // sumcheck over eq(point, x) * f(x) with the converted LSB kernels; the
    // monomial track folds in lockstep and must agree with the evaluation
    // track after every round
    let mut eval_form: Vec<E> = evals.iter().map(|e| E::from_base(*e)).collect();
    let mut eval_slice = &mut eval_form[..];
    let mut eq_vec = eq_full.clone();
    let mut eq_slice = &mut eq_vec[..];
    let mut mono_form: Vec<E> = coeffs.iter().map(|c| E::from_base(*c)).collect();
    let mut mono_buffer: Vec<E> = Vec::with_capacity(size / 2);
    let mut running = claim;
    let mut challenges_drawn: Vec<E> = Vec::new();
    for round in 0..num_vars {
        let (f0, f1, _f_half) =
            special_three_point_eval::<F, E>(&eval_slice[..], &eq_slice[..], &worker);
        let mut s01 = f0;
        s01.add_assign(&f1);
        assert_eq!(s01, running, "round {round} claim chaining");
        // deterministic "challenge"
        let r = E::from_base(F::from_nonreduced_u32((round * 7 + 3) as u32));
        challenges_drawn.push(r);
        // next claim from the quadratic through (f0, f1) plus the half point
        // is what production does; here evaluate directly after folding
        eval_slice = fold_evaluation_form::<F, E>(eval_slice, &r, &worker);
        eq_slice = fold_eq_poly::<F, E>(eq_slice, &r, &worker);
        fold_monomial_form(&mut mono_form, &mut mono_buffer, &r, &worker);
        // monomial track consistency each round
        let mut mono_as_evals = mono_form.clone();
        multivariate_coeffs_into_hypercube_evals(
            &mut mono_as_evals,
            mono_form.len().trailing_zeros(),
        );
        assert_eq!(
            &mono_as_evals[..],
            &eval_slice[..],
            "round {round} monomial/evaluation track divergence"
        );
        // new running claim = sum over remaining cube of eq * f
        let mut next = E::ZERO;
        for (e, w) in eval_slice.iter().zip(eq_slice.iter()) {
            let mut t = *e;
            t.mul_assign(w);
            next.add_assign(&t);
        }
        running = next;
    }
    assert_eq!(eval_slice.len(), 1);
    // final: f(r0, r1, r2) * eq(point, r) == running claim
    let mut expected = eval_slice[0];
    expected.mul_assign(&eq_slice[0]);
    assert_eq!(expected, running, "final at-point identity");
    // and the monomial form collapsed to the same value
    assert_eq!(mono_form.len(), 1);
    assert_eq!(mono_form[0], eval_slice[0], "final monomial value");

    // ---- WHIR-style codeword fold, one round ----
    // fold the codeword by r0 pairing v(x), v(-x):
    //   folded(x^2) = (v(x) + v(-x)) / 2 + r * (v(x) - v(-x)) / (2x)
    // and compare against the NTT of the r0-folded monomial form on the
    // half domain (generator w^2)
    let r0 = challenges_drawn[0];
    let mut folded_mono: Vec<E> = coeffs.iter().map(|c| E::from_base(*c)).collect();
    let mut buf: Vec<E> = Vec::with_capacity(size / 2);
    fold_monomial_form(&mut folded_mono, &mut buf, &r0, &worker);

    let half_domain = domain_size / 2;
    let two_inv = F::from_nonreduced_u32(2).inverse().unwrap();
    for i in 0..half_domain {
        let x = generator.pow(i as u32);
        let v_pos = rs_code_word[i];
        let v_neg = rs_code_word[i + half_domain];
        let mut even = v_pos;
        even.add_assign(&v_neg);
        even.mul_assign(&two_inv);
        let mut odd = v_pos;
        odd.sub_assign(&v_neg);
        odd.mul_assign(&two_inv);
        odd.mul_assign(&x.inverse().unwrap());
        let mut folded_val = r0;
        folded_val.mul_assign_by_base(&odd);
        folded_val.add_assign(&E::from_base(even));
        // evaluate the folded monomial form (univariate, natural exponent
        // order) at x^2
        let mut x2 = x;
        x2.square();
        let mut acc = E::ZERO;
        let mut p = F::ONE;
        for c in folded_mono.iter() {
            let mut t = *c;
            t.mul_assign_by_base(&p);
            acc.add_assign(&t);
            p.mul_assign(&x2);
        }
        assert_eq!(
            folded_val, acc,
            "codeword fold vs folded monomial at half-domain index {i}"
        );
    }
}

/// Computational check (small poly): the width-3 uniskip fold
/// `sum_j L_j(r) * f[j]` must equal the multilinear evaluated at a PROPER
/// 3-coordinate point. Candidates: standard-basis eq at (r, r^2, r^4) in
/// both orders, and the domain (1/omega hypercube) eq at the same points.
#[test]
fn quick_uniskip_point_equivalence() {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::uniskip::uniskip8_fold_weights;
    use crate::gkr::sumcheck::eq_poly::{
        make_domain_eq_table_lsb_first, make_eq_table_lsb_first,
    };
    let worker = Worker::new_with_num_threads(1);
    let f: Vec<E> = (0..8u32)
        .map(|i| E::from_base(F::from_nonreduced_u32(i * i * 7 + i * 13 + 5)))
        .collect();
    let r = E::from_base(F::from_nonreduced_u32(987654321));
    let omega16 = domain_generator_for_size::<F>(16);

    let lw = uniskip8_fold_weights::<F, E>(&r, omega16);
    let mut fold = E::ZERO;
    for (w, v) in lw.iter().zip(f.iter()) {
        let mut t = *w;
        t.mul_assign(v);
        fold.add_assign(&t);
    }

    let mut r2 = r;
    r2.square();
    let mut r4 = r2;
    r4.square();
    let dot = |eq: &[E]| -> E {
        let mut acc = E::ZERO;
        for (w, v) in eq.iter().zip(f.iter()) {
            let mut t = *w;
            t.mul_assign(v);
            acc.add_assign(&t);
        }
        acc
    };

    // lambda coordinates (z - 1)/(omega - 1) for per-variable domains
    let lam = |z: E, omega: F| -> E {
        let mut num = z;
        num.sub_assign(&E::ONE);
        let mut den = omega;
        den.sub_assign(&F::ONE);
        let mut v = num;
        v.mul_assign_by_base(&den.inverse().unwrap());
        v
    };
    let mut w8 = omega16;
    w8.square();
    let mut w4 = w8;
    w4.square();
    let mut w2 = w4;
    w2.square();
    let f_rev: Vec<E> = (0..8usize)
        .map(|j| {
            let br = ((j & 1) << 2) | (j & 2) | ((j >> 2) & 1);
            f[br]
        })
        .collect();
    let dot_rev = |eq: &[E]| -> E {
        let mut acc = E::ZERO;
        for (w, v) in eq.iter().zip(f_rev.iter()) {
            let mut t = *w;
            t.mul_assign(v);
            acc.add_assign(&t);
        }
        acc
    };

    let points: Vec<(String, [E; 3])> = vec![
        ("(r,r2,r4)".into(), [r, r2, r4]),
        ("(r4,r2,r)".into(), [r4, r2, r]),
        (
            "lam(r|w8),lam(r2|w4),lam(r4|w2)".into(),
            [lam(r, w8), lam(r2, w4), lam(r4, w2)],
        ),
        (
            "lam(r4|w2),lam(r2|w4),lam(r|w8)".into(),
            [lam(r4, w2), lam(r2, w4), lam(r, w8)],
        ),
        (
            "lam(r|w2),lam(r2|w4),lam(r4|w8)".into(),
            [lam(r, w2), lam(r2, w4), lam(r4, w8)],
        ),
        (
            "lam(r4|w8),lam(r2|w4),lam(r|w2)".into(),
            [lam(r4, w8), lam(r2, w4), lam(r, w2)],
        ),
    ];
    let mut candidates: Vec<(String, E)> = Vec::new();
    for (pname, pt) in points.iter() {
        let std_eq = make_eq_table_lsb_first::<E>(&pt[..], &worker);
        let dom_eq = make_domain_eq_table_lsb_first::<F, E>(&pt[..]);
        candidates.push((format!("std {pname} f-nat"), dot(&std_eq)));
        candidates.push((format!("std {pname} f-rev"), dot_rev(&std_eq)));
        candidates.push((format!("dom {pname} f-nat"), dot(&dom_eq)));
        candidates.push((format!("dom {pname} f-rev"), dot_rev(&dom_eq)));
    }
    let mut matched: Vec<String> = vec![];
    for (name, v) in candidates.iter() {
        if *v == fold {
            matched.push(name.clone());
            println!("{name}: MATCH");
        }
    }
    // ESTABLISHED: the H-value-interpolation fold (current kernels) matches
    // NO per-coordinate point in either basis -- it binds a curve.
    assert!(
        matched.is_empty(),
        "unexpected: H-interpolation fold matched {matched:?}"
    );

    // THE STANDARD UNIVARIATE SKIP (monomial map: exponent bit b = variable
    // b) binds EXACTLY (r, r^2, r^4) in the STANDARD basis. Its per-group
    // univariate is f_hat(Y) = sum_m c_m Y^m (the zeta-inverse coefficients
    // of the 8 values), and f_hat(r) = f(r, r^2, r^4). Verify with the SAME
    // encode pieces the commitment uses: zeta-inverse -> padded bitrev ->
    // NTT16 gives f_hat on the 16-point domain; barycentric interpolation of
    // those 16 values at r must equal the standard-basis evaluation.
    let mut coeffs8: Vec<E> = f.clone();
    crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs(
        &mut coeffs8,
        3,
    );
    // direct Horner of f_hat at r (exponent = index)
    let mut fhat_r = E::ZERO;
    let mut pw = E::ONE;
    for c in coeffs8.iter() {
        let mut t = *c;
        t.mul_assign(&pw);
        fhat_r.add_assign(&t);
        pw.mul_assign(&r);
    }
    let expected = dot(&make_eq_table_lsb_first::<E>(&[r, r2, r4], &worker));
    assert_eq!(
        fhat_r, expected,
        "standard-skip binding: f_hat(r) == f(r, r^2, r^4) in the standard basis"
    );
    println!("standard univariate skip binds (r, r^2, r^4): CONFIRMED");
}

