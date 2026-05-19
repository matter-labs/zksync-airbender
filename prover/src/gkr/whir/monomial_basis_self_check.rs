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

    // it should be equal to our initial claim
    let eq_table_at_zero_inf = eqs_at_zero_inf.last().unwrap();
    let mut output_at_random_point = F::ZERO;
    for i in 0..size {
        let mut t = output[i];
        t.mul_assign(&eq_table_at_zero_inf[i]);
        output_at_random_point.add_assign(&t);
        dbg!(t);
    }
    dbg!(output_at_random_point);

    // there are multiple ways to "save" on computations in sumcheck of the special form
    // like we have - \sum_{ x = {0/inf}^N } eq(x, r) * a(x) * b(x), and below we will split it as G(X) = \sum_x eq(X, r0) * eq(x, r1, ...) * A(X, x) * B(X, x)

    // We always have the following constraints to consider
    // claim = G(0) + G(inf)
    // eq_{0/inf}(X, r0) == 1 + r0 * X

    // and in general G(X) = (r0 * X + 1) * (c * X^2 + d * X + e)
    // where quadratic part comes from the A(X) * B(X)

    // note that G(0) and G(infinity) are nice to compute in initial rounds as they are
    // just exactly the output values of the GKR layer, so we will do the following trick
    // - we only compute relations like claim = output(r) =  \sum_{x = {0/inf}^N} eq_{0/inf}(x, r) * a(x) * b(x)
    // - instead we can write it as (change of basis)
    // claim = output(r) = \sum_{x0 = {0/1}} \sum_{x1... = {0/inf}^{N-1}} eq_{0/1}(x0, r0) eq_{0/inf}(x1..., r1...) * a(x) * b(x),
    // and if we would want to compute it naively we would need to materialize the table for a(x0 = 0/1, x1 = 0/inf, ...)
    // and so G(X) = \sum_{x1.. = {0/inf}^{N-1}} eq_{0/1}(X, r0) eq_{0/inf}(x1..., r1...) * a(X, x1...) * b(X, x1...),
    // but instead it gives us a right to use the fact that claim = G(0) + G(1)
    // so we choose our missing evaluation point for interpolation to be G(inf), and in the first sumcheck round we only have a(x) * b(x)
    // at the "defining" hypercube, so we can use those values directly.
    // In the later rounds we can use exactly the same trick, and we will need to compute something like
    // G_1(X) = prefactor * \sum_{x2.. = {0/inf}^{N-2}} eq_{0/1}(X, r1) eq_{0/inf}(x2..., r2...) * a(t, X, x2...) * b(t, X, x2...),
    // that again has a nice property that we do not need to get some "mixed" values like a(t, 1, x2...) that would require reading both
    // a(t, 0, x2...) and a(t, inf, x2...) from our poly storage format (so - reading 2 values at once). Instead we can
    // read only a(t, 0, x2...) when computing G(0) and a(t, inf, x2...) for G(inf)
    
    // Here we self-check our second approach

    let eq_table_at_zero_inf = eqs_at_zero_inf.last().unwrap();
    let mut claim = F::ZERO;
    let mut g_0_self_check = F::ZERO;

    // we honestly compute our first claim as 
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

        dbg!((out_at_0, out_at_1));

        claim.add_assign(&out_at_0);
        claim.add_assign(&out_at_1);

        g_0_self_check.add_assign(&out_at_0);
    }

    dbg!(claim);

    panic!();

    // assert_eq!(claim, output_at_random_point);

    {
        let all_eq_except_last = eqs_at_zero_inf.iter().rev().skip(1).next().unwrap().clone();
        let mut mixed_eq = vec![F::ZERO; size].into_boxed_slice();

        // eq_{0/1} is xy + (1-x)(1-y)
        let mut eq_at_0 = F::ONE;
        eq_at_0.sub_assign(&challenge_coordiantes[0]);

        let eq_at_1 = challenge_coordiantes[0];

        for index in 0..size/2 {
            let mut left = all_eq_except_last[index];
            let mut right = left;
            left.mul_assign(&eq_at_0);
            right.mul_assign(&eq_at_1);
            mixed_eq[index] = left;
            mixed_eq[index + size/2] = right;
        }

        let mut alt_claim = F::ZERO;
        for i in 0..size / 2 {
            let a_at_0 = a[i];
            let b_at_0 = b[i];
            let a_at_inf = a[i + size / 2];
            let b_at_inf = b[i + size / 2];

            let mut a_at_1 = a_at_inf;
            a_at_1.add_assign(&a_at_0);
            let mut b_at_1 = b_at_inf;
            b_at_1.add_assign(&b_at_0);

            let naive_out_at_0 = output[i];

            let mut out_at_0 = a_at_0;
            out_at_0.mul_assign(&b_at_0);
            let mut out_at_1 = a_at_1;
            out_at_1.mul_assign(&b_at_1);

            assert_eq!(naive_out_at_0, out_at_0);

            let eq_at_0 = mixed_eq[i];
            let eq_at_1 = mixed_eq[i + size / 2];

            dbg!((eq_at_0, eq_at_1));

            out_at_0.mul_assign(&eq_at_0);
            out_at_1.mul_assign(&eq_at_1);

            alt_claim.add_assign(&out_at_0);
            alt_claim.add_assign(&out_at_1);
        }

        dbg!(alt_claim);

        assert_eq!(alt_claim, claim);
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
