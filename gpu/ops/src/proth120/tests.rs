use super::*;
use era_cudart::memory::{memory_copy_async, memory_set_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use field::{Field, PrimeField};
use gpu_core::primitives::field::PR;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::panic::{catch_unwind, AssertUnwindSafe};

const P: u128 = PR::ORDER;
const SEED: u64 = 0x9120_0001;
const GUARD: usize = 16;
const SENTINEL: u8 = 0xAA;
const RAW_INVALID: u32 = 0xFFFF_FFFF;

type Wide = [u32; 8];

fn seeded_rng() -> StdRng {
    StdRng::seed_from_u64(SEED)
}

fn random_pr(rng: &mut StdRng) -> PR {
    loop {
        let raw = rng.random::<u128>() >> 5;
        if raw < P {
            return PR::from_raw_u128(raw);
        }
    }
}

fn random_nonzero_pr(rng: &mut StdRng) -> PR {
    loop {
        let value = random_pr(rng);
        if !value.is_zero() {
            return value;
        }
    }
}

fn random_below(rng: &mut StdRng, bound: u128) -> u128 {
    rng.random_range(0..bound)
}

fn words(x: u128) -> [u32; 4] {
    core::array::from_fn(|i| (x >> (32 * i)) as u32)
}

fn from_words(w: [u32; 4]) -> u128 {
    w.iter().rev().fold(0, |acc, &x| (acc << 32) | x as u128)
}

fn bytes_of<T>(values: &[T]) -> &[u8] {
    unsafe { core::slice::from_raw_parts(values.as_ptr().cast(), core::mem::size_of_val(values)) }
}

fn mont_r() -> u128 {
    PR::ONE.0
}

fn mont_r2() -> u128 {
    PR::new(mont_r()).0
}

fn add(x: PR, y: PR) -> PR {
    *x.clone().add_assign(&y)
}

fn sub(x: PR, y: PR) -> PR {
    *x.clone().sub_assign(&y)
}

fn mul(x: PR, y: PR) -> PR {
    *x.clone().mul_assign(&y)
}

fn natural_values() -> Vec<u128> {
    vec![
        0,
        1,
        2,
        42,
        P / 2,
        P - 1,
        P,
        P + 1,
        2 * P - 1,
        2 * P,
        36 * P - 1,
        36 * P,
        36 * P + 1,
        u128::MAX,
        1 << 64,
        1 << 96,
        1 << 127,
        mont_r(),
        mont_r2(),
    ]
}

fn canonical_values() -> Vec<PR> {
    let mut raws = vec![0, 1, 2, P - 2, P - 1, mont_r(), PR::TWO.0, PR::MINUS_ONE.0];
    for shift in [32, 64, 96, 120] {
        let base = 1u128 << shift;
        raws.extend([base - 1, base, base + 1]);
    }
    let mut values: Vec<PR> = raws.into_iter().map(PR::from_raw_u128).collect();
    values.extend(
        natural_values()
            .into_iter()
            .map(PR::from_u128_with_reduction),
    );
    values
}

fn exponents() -> Vec<u128> {
    vec![
        0,
        1,
        2,
        3,
        17,
        31,
        32,
        255,
        (1 << 32) - 1,
        1 << 32,
        1 << 64,
        1 << 96,
        1 << 120,
        P - 2,
        P - 1,
        u128::MAX,
    ]
}

fn extract_oracle(natural: u128, offset: u32, count: u32) -> u32 {
    if count == 0 {
        return 0;
    }
    let mask = if count == 32 {
        u32::MAX
    } else {
        (1u32 << count) - 1
    };
    ((natural >> offset) as u32) & mask
}

fn alloc_guarded<T>(len: usize, stream: &CudaStream) -> DeviceAllocation<T> {
    let mut allocation = DeviceAllocation::alloc(len + 2 * GUARD).unwrap();
    memory_set_async(unsafe { allocation.transmute_mut() }, SENTINEL, stream).unwrap();
    allocation
}

fn upload_guarded<T: Copy>(values: &[T], stream: &CudaStream) -> DeviceAllocation<T> {
    let mut allocation = alloc_guarded(values.len(), stream);
    memory_copy_async(&mut allocation[GUARD..GUARD + values.len()], values, stream).unwrap();
    allocation
}

fn read_guarded<T: Copy + Default>(
    allocation: &DeviceAllocation<T>,
    len: usize,
    what: &str,
    stream: &CudaStream,
) -> Vec<T> {
    let mut host = vec![T::default(); len + 2 * GUARD];
    memory_copy_async(&mut host, allocation, stream).unwrap();
    stream.synchronize().unwrap();
    let (head, rest) = host.split_at(GUARD);
    let (body, tail) = rest.split_at(len);
    assert!(
        bytes_of(head)
            .iter()
            .chain(bytes_of(tail))
            .all(|&b| b == SENTINEL),
        "{what}: guard overwritten"
    );
    body.to_vec()
}

fn panic_message(f: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a panic");
    if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        panic!("non-string panic payload")
    }
}

fn field_input(a: PR, b: PR, c: PR, exp: u128, natural: u128, extract: (u32, u32)) -> PrProbeInput {
    PrProbeInput {
        a,
        b,
        c,
        exp_u32: exp as u32,
        exp_le: words(exp),
        natural_le: words(natural),
        extract_offset: extract.0,
        extract_count: extract.1,
        _pad: 0,
    }
}

fn expected_field_output(input: &PrProbeInput) -> PrProbeOutput {
    let (a, b, c) = (input.a, input.b, input.c);
    let natural = from_words(input.natural_le);
    PrProbeOutput {
        add: add(a, b),
        sub: sub(a, b),
        mul: mul(a, b),
        sqr: *a.clone().square(),
        neg: *a.clone().negate(),
        dbl: *a.clone().double(),
        inv: a.inverse().unwrap_or(PR::ZERO),
        pow_u32: a.pow(input.exp_u32),
        pow_u128: a.pow_u128(from_words(input.exp_le)),
        fma: add(mul(a, b), c),
        fms: sub(mul(a, b), c),
        from_natural: PR::from_u128_with_reduction(natural),
        pow_log2_8: a.pow_u128(1 << 8),
        scalar_mul: mul(PR::from_u32_with_reduction(input.exp_u32), a),
        half: mul(a, PR::TWO.inverse().unwrap()),
        zero: PR::ZERO,
        one: PR::ONE,
        two: PR::TWO,
        be_bytes: a.to_u128().to_be_bytes(),
        eq: (a == b) as u32,
        is_zero: a.is_zero() as u32,
        extract: extract_oracle(natural, input.extract_offset, input.extract_count),
        operator_mismatch: 0,
    }
}

fn field_values(o: &PrProbeOutput) -> [(&'static str, PR); 18] {
    [
        ("add", o.add),
        ("sub", o.sub),
        ("mul", o.mul),
        ("sqr", o.sqr),
        ("neg", o.neg),
        ("dbl", o.dbl),
        ("inv", o.inv),
        ("pow_u32", o.pow_u32),
        ("pow_u128", o.pow_u128),
        ("fma", o.fma),
        ("fms", o.fms),
        ("from_natural", o.from_natural),
        ("pow_log2_8", o.pow_log2_8),
        ("scalar_mul", o.scalar_mul),
        ("half", o.half),
        ("zero", o.zero),
        ("one", o.one),
        ("two", o.two),
    ]
}

fn run_field_probe(inputs: &[PrProbeInput]) -> Vec<PrProbeOutput> {
    let stream = CudaStream::default();
    let d_inputs = upload_guarded(inputs, &stream);
    let mut d_outputs = alloc_guarded::<PrProbeOutput>(inputs.len(), &stream);
    pr_field_probe(
        &d_inputs[GUARD..GUARD + inputs.len()],
        &mut d_outputs[GUARD..GUARD + inputs.len()],
        &stream,
    )
    .unwrap();
    let outputs = read_guarded(&d_outputs, inputs.len(), "field probe output", &stream);
    let inputs_back = read_guarded(&d_inputs, inputs.len(), "field probe input", &stream);
    assert!(inputs_back == inputs, "field probe input modified");
    outputs
}

fn check_field_probe(inputs: &[PrProbeInput]) -> Vec<PrProbeOutput> {
    let outputs = run_field_probe(inputs);
    for (i, (input, output)) in inputs.iter().zip(outputs.iter()).enumerate() {
        for (name, value) in field_values(output) {
            assert!(
                value.0 < P,
                "record {i}: {name} = {:#x} is not canonical",
                value.0
            );
        }
        assert_eq!(
            *output,
            expected_field_output(input),
            "record {i}: {input:?}"
        );
    }
    outputs
}

#[test]
fn pr_arithmetic_cpu_parity() {
    let mut rng = seeded_rng();
    let edges = canonical_values();
    let exps = exponents();
    let naturals = natural_values();
    let mut inputs = vec![];
    for (i, &a) in edges.iter().enumerate() {
        for (j, &b) in edges.iter().enumerate() {
            let c = edges[(i + j) % edges.len()];
            inputs.push(field_input(
                a,
                b,
                c,
                exps[j % exps.len()],
                naturals[i % naturals.len()],
                (0, 32),
            ));
        }
    }
    for _ in 0..4096 {
        let (a, b, c) = (
            random_pr(&mut rng),
            random_pr(&mut rng),
            random_pr(&mut rng),
        );
        inputs.push(field_input(a, b, c, rng.random(), rng.random(), (96, 32)));
    }
    check_field_probe(&inputs);

    let triples: Vec<(PR, PR, PR)> = (0..256)
        .map(|_| {
            (
                random_pr(&mut rng),
                random_pr(&mut rng),
                random_pr(&mut rng),
            )
        })
        .collect();
    let first: Vec<PrProbeInput> = triples
        .iter()
        .flat_map(|&(a, b, c)| {
            [
                field_input(a, b, c, 0, 0, (0, 0)),
                field_input(b, a, c, 0, 0, (0, 0)),
                field_input(b, c, a, 0, 0, (0, 0)),
                field_input(a, c, b, 0, 0, (0, 0)),
            ]
        })
        .collect();
    let first = check_field_probe(&first);
    let second: Vec<PrProbeInput> = triples
        .iter()
        .enumerate()
        .flat_map(|(t, &(a, _, c))| {
            let [ab, _, bc, ac] = [0, 1, 2, 3].map(|k| first[4 * t + k]);
            [
                field_input(ab.mul, c, c, 0, 0, (0, 0)),
                field_input(a, bc.mul, c, 0, 0, (0, 0)),
                field_input(a, bc.add, c, 0, 0, (0, 0)),
                field_input(ab.mul, ac.mul, c, 0, 0, (0, 0)),
            ]
        })
        .collect();
    let second = check_field_probe(&second);
    for t in 0..triples.len() {
        let [ab, ba, _, _] = [0, 1, 2, 3].map(|k| first[4 * t + k]);
        assert_eq!(ab.mul, ba.mul, "triple {t}: mul not commutative");
        assert_eq!(ab.add, ba.add, "triple {t}: add not commutative");
        let [ab_c, a_bc, a_b_plus_c, ab_plus_ac] = [0, 1, 2, 3].map(|k| second[4 * t + k]);
        assert_eq!(ab_c.mul, a_bc.mul, "triple {t}: mul not associative");
        assert_eq!(
            a_b_plus_c.mul, ab_plus_ac.add,
            "triple {t}: not distributive"
        );
    }
}

#[test]
fn pr_conversion_cpu_parity() {
    let mut rng = seeded_rng();
    let mut naturals = natural_values();
    naturals.extend((0..4096).map(|_| rng.random::<u128>()));
    let inputs: Vec<PrProbeInput> = naturals
        .iter()
        .map(|&n| {
            field_input(
                PR::from_u128_with_reduction(n),
                PR::ONE,
                PR::ZERO,
                1,
                n,
                (0, 0),
            )
        })
        .collect();
    let first = check_field_probe(&inputs);
    let round_trip: Vec<PrProbeInput> = first
        .iter()
        .map(|o| field_input(o.from_natural, PR::ONE, PR::ZERO, 1, 0, (0, 0)))
        .collect();
    let second = check_field_probe(&round_trip);
    for (i, (&n, o)) in naturals.iter().zip(second.iter()).enumerate() {
        assert_eq!(o.be_bytes, (n % P).to_be_bytes(), "natural {i} = {n:#x}");
    }

    let stream = CudaStream::default();
    let values = canonical_values();
    let d_values = upload_guarded(&values, &stream);
    let back = read_guarded(&d_values, values.len(), "round trip", &stream);
    assert_eq!(bytes_of(&back), bytes_of(&values));
}

#[test]
fn pr_pow_inverse_cpu_parity() {
    let mut rng = seeded_rng();
    let mut bases = canonical_values();
    bases.extend((0..256).map(|_| random_nonzero_pr(&mut rng)));
    let exps = exponents();
    let mut inputs = vec![];
    for &a in bases.iter() {
        for &e in exps.iter() {
            inputs.push(field_input(a, a, a, e, 0, (0, 0)));
        }
        inputs.push(field_input(a, a, a, rng.random(), 0, (0, 0)));
    }
    let outputs = check_field_probe(&inputs);
    for (input, output) in inputs.iter().zip(outputs.iter()) {
        if input.a.is_zero() {
            assert_eq!(output.inv, PR::ZERO);
        } else {
            assert_eq!(mul(output.inv, input.a), PR::ONE);
        }
    }
}

#[test]
fn pr_root_arithmetic_cpu_parity() {
    let generators = PR::TWO_ADICITY_GENERATORS;
    let inverses = PR::TWO_ADICITY_GENERATORS_INVERSED;
    let mut inputs = vec![];
    for k in 0..=120usize {
        let previous = generators[k.saturating_sub(1)];
        inputs.push(field_input(
            generators[k],
            inverses[k],
            previous,
            1u128 << k,
            0,
            (0, 0),
        ));
        if k > 0 {
            inputs.push(field_input(
                generators[k],
                inverses[k],
                previous,
                1u128 << (k - 1),
                0,
                (0, 0),
            ));
        }
    }
    let outputs = check_field_probe(&inputs);
    let mut records = inputs.iter().zip(outputs.iter());
    for k in 0..=120usize {
        let (_, full) = records.next().unwrap();
        assert_eq!(full.pow_u128, PR::ONE, "generator[{k}]^(2^{k})");
        assert_eq!(full.mul, PR::ONE, "generator[{k}] * inverse[{k}]");
        assert_eq!(full.inv, inverses[k], "inv(generator[{k}])");
        if k > 0 {
            assert_eq!(full.sqr, generators[k - 1], "generator[{k}]^2");
            let (_, half) = records.next().unwrap();
            assert_eq!(half.pow_u128, PR::MINUS_ONE, "generator[{k}]^(2^{})", k - 1);
        } else {
            assert_eq!(generators[0], PR::ONE);
        }
    }
}

fn w_from(x: u128) -> Wide {
    let w = words(x);
    [w[0], w[1], w[2], w[3], 0, 0, 0, 0]
}

fn w_from_pair(lo: u128, hi: u128) -> Wide {
    let (l, h) = (words(lo), words(hi));
    [l[0], l[1], l[2], l[3], h[0], h[1], h[2], h[3]]
}

fn w_lo(w: &Wide) -> u128 {
    from_words([w[0], w[1], w[2], w[3]])
}

fn w_hi(w: &Wide) -> u128 {
    from_words([w[4], w[5], w[6], w[7]])
}

fn w_below(rng: &mut StdRng, bound: &Wide) -> Wide {
    loop {
        let candidate = w_from_pair(rng.random(), random_below(rng, w_hi(bound) + 1));
        if w_sub(&candidate, bound).1 {
            return candidate;
        }
    }
}

fn w_add(a: &Wide, b: &Wide) -> (Wide, bool) {
    let mut r = [0u32; 8];
    let mut carry = 0u64;
    for i in 0..8 {
        let s = a[i] as u64 + b[i] as u64 + carry;
        r[i] = s as u32;
        carry = s >> 32;
    }
    (r, carry != 0)
}

fn w_sub(a: &Wide, b: &Wide) -> (Wide, bool) {
    let mut r = [0u32; 8];
    let mut borrow = false;
    for i in 0..8 {
        let (d0, b0) = a[i].overflowing_sub(b[i]);
        let (d1, b1) = d0.overflowing_sub(borrow as u32);
        r[i] = d1;
        borrow = b0 || b1;
    }
    (r, borrow)
}

fn w_mul(a: u128, b: u128) -> Wide {
    let (a, b) = (words(a), words(b));
    let mut r = [0u32; 8];
    for i in 0..4 {
        let mut carry = 0u64;
        for j in 0..4 {
            let t = r[i + j] as u64 + a[i] as u64 * b[j] as u64 + carry;
            r[i + j] = t as u32;
            carry = t >> 32;
        }
        r[i + 4] = carry as u32;
    }
    r
}

fn np(n: u32) -> u128 {
    n as u128 * P
}

fn np2(n: u32) -> Wide {
    w_mul(np(n), P)
}

fn reduce_n(x: u128, n: u32) -> u128 {
    if n != 0 && x >= np(n) {
        x - np(n)
    } else {
        x
    }
}

fn reduce_wide_n(x: &Wide, n: u32) -> Wide {
    if n == 0 {
        return *x;
    }
    let (d, borrow) = w_sub(x, &np2(n));
    if borrow {
        *x
    } else {
        d
    }
}

fn w_lt(a: &Wide, b: &Wide) -> bool {
    w_sub(a, b).1
}

fn edge_values() -> Vec<u128> {
    let mut values = natural_values();
    values.extend(canonical_values().iter().map(|v| v.0));
    values.sort_unstable();
    values.dedup();
    values
}

fn edge_wides() -> Vec<Wide> {
    let mut values: Vec<Wide> = edge_values()
        .into_iter()
        .flat_map(|x| [w_from(x), w_from_pair(0, x), w_from_pair(x, x)])
        .collect();
    values.sort_unstable();
    values.dedup();
    values
}

fn edge_pairs<T: Copy>(values: &[T]) -> Vec<(T, T)> {
    values
        .iter()
        .flat_map(|&x| values.iter().map(move |&y| (x, y)))
        .collect()
}

fn redc_reference(w: &Wide) -> u128 {
    let radix = PR::new(1 << 32);
    let mut acc = PR::ZERO;
    for i in (0..8).rev() {
        acc.mul_assign(&radix);
        acc.add_assign(&PR::new(w[i] as u128));
    }
    let mut r = PR::new(acc.to_u128());
    r.mul_assign(&PR::new(mont_r()).inverse().unwrap());
    r.to_u128()
}

fn montmul_reference(x: u128, y: u128) -> u128 {
    mul(PR::from_raw_u128(x), PR::from_raw_u128(y)).0
}

const OP_ADD_SUB_LIMBS: u32 = 0;
const OP_MODULUS: u32 = 1;
const OP_MODULUS_SQUARED: u32 = 2;
const OP_REDUCE: u32 = 3;
const OP_REDUCE_WIDE: u32 = 4;
const OP_ADD_PICK: u32 = 5;
const OP_SUB_PICK: u32 = 6;
const OP_ADD_WIDE: u32 = 7;
const OP_SUB_WIDE: u32 = 8;
const OP_MULTIPLY_RAW: u32 = 9;
const OP_SQR_RAW: u32 = 10;
const OP_MUL_WIDE: u32 = 11;
const OP_MONTMUL_RAW: u32 = 12;
const OP_MUL_PICK: u32 = 13;
const OP_SQR_PICK: u32 = 14;
const OP_REDC_WIDE_INPLACE: u32 = 15;
const OP_REDC_WIDE: u32 = 16;

fn raw_op_width(op: u32) -> &'static [u32] {
    match op {
        OP_ADD_SUB_LIMBS => &[4, 8],
        OP_MODULUS_SQUARED | OP_REDUCE_WIDE | OP_ADD_WIDE | OP_SUB_WIDE | OP_REDC_WIDE_INPLACE
        | OP_REDC_WIDE => &[8],
        _ => &[4],
    }
}

fn raw_op_ns(op: u32) -> &'static [u32] {
    match op {
        OP_ADD_SUB_LIMBS | OP_MULTIPLY_RAW | OP_SQR_RAW | OP_MONTMUL_RAW | OP_REDC_WIDE_INPLACE => {
            &[0]
        }
        _ => &[0, 1, 2, 4],
    }
}

fn raw_op_flags(op: u32) -> &'static [u32] {
    match op {
        OP_ADD_SUB_LIMBS => &[0, 1, 2, 3],
        _ => &[0],
    }
}

enum RawExpect {
    Exact { r: Wide, carry: Option<bool> },
    Lazy { canonical: u128 },
}

fn expected_raw(input: &PrRawProbeInput) -> RawExpect {
    let (a, b, n) = (&input.a, &input.b, input.n);
    let (x, y) = (w_lo(a), w_lo(b));
    let exact = |r: Wide| RawExpect::Exact { r, carry: None };
    let narrow = |r: u128| RawExpect::Exact {
        r: w_from(r),
        carry: None,
    };
    match input.op {
        OP_ADD_SUB_LIMBS => {
            let subtract = input.flags & 1 != 0;
            let carry_out = input.flags & 2 != 0;
            let (r, c) = if input.width == 4 {
                let (r, c) = if subtract {
                    x.overflowing_sub(y)
                } else {
                    x.overflowing_add(y)
                };
                (w_from(r), c)
            } else if subtract {
                w_sub(a, b)
            } else {
                w_add(a, b)
            };
            RawExpect::Exact {
                r,
                carry: Some(carry_out && c),
            }
        }
        OP_MODULUS => narrow(np(n)),
        OP_MODULUS_SQUARED => exact(if n == 0 { [0; 8] } else { np2(n) }),
        OP_REDUCE => narrow(reduce_n(x, n)),
        OP_REDUCE_WIDE => exact(reduce_wide_n(a, n)),
        OP_ADD_PICK => narrow(reduce_n(x.wrapping_add(y), n)),
        OP_SUB_PICK => narrow(if x >= y || n == 0 {
            x.wrapping_sub(y)
        } else {
            x.wrapping_sub(y).wrapping_add(np(n))
        }),
        OP_ADD_WIDE => exact(reduce_wide_n(&w_add(a, b).0, n)),
        OP_SUB_WIDE => {
            let (d, borrow) = w_sub(a, b);
            exact(if borrow && n != 0 {
                w_add(&d, &np2(n)).0
            } else {
                d
            })
        }
        OP_MULTIPLY_RAW => exact(w_mul(x, y)),
        OP_SQR_RAW => exact(w_mul(x, x)),
        OP_MUL_WIDE => exact(reduce_wide_n(&w_mul(x, y), n)),
        OP_MONTMUL_RAW => RawExpect::Lazy {
            canonical: montmul_reference(x, y),
        },
        OP_MUL_PICK if n == 1 => narrow(montmul_reference(x, y)),
        OP_MUL_PICK => RawExpect::Lazy {
            canonical: montmul_reference(x, y),
        },
        OP_SQR_PICK if n == 1 => narrow(montmul_reference(x, x)),
        OP_SQR_PICK => RawExpect::Lazy {
            canonical: montmul_reference(x, x),
        },
        OP_REDC_WIDE_INPLACE => RawExpect::Lazy {
            canonical: redc_reference(a),
        },
        OP_REDC_WIDE if n == 1 => narrow(redc_reference(a)),
        OP_REDC_WIDE => RawExpect::Lazy {
            canonical: redc_reference(a),
        },
        _ => unreachable!(),
    }
}

fn raw_operands(op: u32, n: u32, width: u32, rng: &mut StdRng) -> Vec<(Wide, Wide)> {
    let full = |rng: &mut StdRng| -> Wide { core::array::from_fn(|_| rng.random()) };
    let canonical = |rng: &mut StdRng| random_below(rng, P);
    let narrow_below = |bound: Option<u128>| -> Vec<Wide> {
        edge_values()
            .into_iter()
            .filter(|&x| bound.is_none_or(|b| x < b))
            .map(w_from)
            .collect()
    };
    let wide_below = |bound: Option<Wide>| -> Vec<Wide> {
        edge_wides()
            .into_iter()
            .filter(|x| bound.is_none_or(|b| w_lt(x, &b)))
            .collect()
    };
    let unary = |values: Vec<Wide>| -> Vec<(Wide, Wide)> {
        values.into_iter().map(|x| (x, [0; 8])).collect()
    };
    let mut cases: Vec<(Wide, Wide)> = vec![];
    match op {
        OP_ADD_SUB_LIMBS => {
            let patterns: [Wide; 6] = [
                [0; 8],
                [u32::MAX; 8],
                [1, 0, 0, 0, 0, 0, 0, 0],
                [u32::MAX, u32::MAX, u32::MAX, u32::MAX, 0, 0, 0, 0],
                [0x5555_5555; 8],
                [0xAAAA_AAAA; 8],
            ];
            for a in patterns.iter() {
                for b in patterns.iter() {
                    cases.push((*a, *b));
                }
            }
            if width == 4 {
                cases.extend(edge_pairs(&narrow_below(None)));
            } else {
                cases.extend(edge_pairs(&wide_below(None)));
            }
            cases.extend((0..1024).map(|_| (full(rng), full(rng))));
        }
        OP_MODULUS | OP_MODULUS_SQUARED => cases.push(([0; 8], [0; 8])),
        OP_REDUCE if n == 0 => {
            cases.extend(unary(narrow_below(None)));
            cases.extend((0..1024).map(|_| (w_from(rng.random()), [0; 8])));
        }
        OP_REDUCE => {
            let m = np(n);
            cases.extend(unary(narrow_below(Some(2 * m))));
            for x in [0, m - 1, m, m + 1, 2 * m - 1] {
                cases.push((w_from(x), [0; 8]));
            }
            cases.extend((0..1024).map(|_| (w_from(random_below(rng, 2 * m)), [0; 8])));
        }
        OP_REDUCE_WIDE if n == 0 => {
            cases.extend(unary(wide_below(None)));
            cases.extend((0..1024).map(|_| (full(rng), [0; 8])));
        }
        OP_REDUCE_WIDE => {
            let m = np2(n);
            let one = w_from(1);
            let two_m = w_add(&m, &m).0;
            cases.extend(unary(wide_below(Some(two_m))));
            for x in [
                [0; 8],
                w_sub(&m, &one).0,
                m,
                w_add(&m, &one).0,
                w_sub(&two_m, &one).0,
            ] {
                cases.push((x, [0; 8]));
            }
            cases.extend((0..1024).map(|_| (w_below(rng, &two_m), [0; 8])));
        }
        OP_ADD_PICK | OP_SUB_PICK if n == 0 => {
            cases.extend(edge_pairs(&narrow_below(None)));
            cases.extend((0..1024).map(|_| (w_from(rng.random()), w_from(rng.random()))));
        }
        OP_ADD_PICK | OP_SUB_PICK => {
            let m = np(n);
            cases.extend(edge_pairs(&narrow_below(Some(m))));
            for x in [0, 1, m - 1] {
                for y in [0, 1, m - 1] {
                    cases.push((w_from(x), w_from(y)));
                }
            }
            cases.extend(
                (0..1024).map(|_| (w_from(random_below(rng, m)), w_from(random_below(rng, m)))),
            );
        }
        OP_ADD_WIDE | OP_SUB_WIDE if n == 0 => {
            cases.extend(edge_pairs(&wide_below(None)));
            cases.extend((0..1024).map(|_| (full(rng), full(rng))));
        }
        OP_ADD_WIDE | OP_SUB_WIDE => {
            let m = np2(n);
            cases.extend(edge_pairs(&wide_below(Some(m))));
            let m_minus_one = w_sub(&m, &w_from(1)).0;
            for x in [[0; 8], w_from(1), m_minus_one] {
                for y in [[0; 8], w_from(1), m_minus_one] {
                    cases.push((x, y));
                }
            }
            cases.extend((0..1024).map(|_| (w_below(rng, &m), w_below(rng, &m))));
        }
        OP_MULTIPLY_RAW | OP_SQR_RAW | OP_MUL_WIDE | OP_MONTMUL_RAW | OP_MUL_PICK | OP_SQR_PICK => {
            let edges = [
                0,
                1,
                2,
                P - 2,
                P - 1,
                mont_r(),
                (1 << 64) - 1,
                1 << 64,
                (1 << 120) + 1,
            ];
            for &x in edges.iter() {
                for &y in edges.iter() {
                    cases.push((w_from(x), w_from(y)));
                }
            }
            if op == OP_SQR_RAW || op == OP_SQR_PICK {
                cases.extend(unary(narrow_below(Some(P))));
            } else {
                cases.extend(edge_pairs(&narrow_below(Some(P))));
            }
            cases.extend((0..1024).map(|_| (w_from(canonical(rng)), w_from(canonical(rng)))));
        }
        OP_REDC_WIDE_INPLACE | OP_REDC_WIDE => {
            let p2 = w_mul(P, P);
            let one = w_from(1);
            let p_r_minus_one = w_sub(&w_from_pair(0, P), &one).0;
            for w in [[0; 8], one, w_sub(&p2, &one).0, p2, p_r_minus_one] {
                cases.push((w, [0; 8]));
            }
            cases.extend(unary(wide_below(Some(w_from_pair(0, P)))));
            cases.extend(
                (0..1024).map(|_| (w_from_pair(rng.random(), random_below(rng, P)), [0; 8])),
            );
        }
        _ => unreachable!(),
    }
    cases
}

fn check_raw_output(input: &PrRawProbeInput, output: &PrRawProbeOutput, i: usize) {
    assert_eq!(output.status, 0, "raw record {i}: {input:?}");
    assert_eq!(output._pad, [0; 2], "raw record {i}: padding");
    match expected_raw(input) {
        RawExpect::Exact { r, carry } => {
            assert_eq!(output.r, r, "raw record {i}: {input:?}");
            match carry {
                Some(c) => assert_eq!(output.carry != 0, c, "raw record {i}: carry, {input:?}"),
                None => assert_eq!(output.carry, 0, "raw record {i}: carry, {input:?}"),
            }
        }
        RawExpect::Lazy { canonical } => {
            let lo = w_lo(&output.r);
            assert!(lo < 2 * P, "raw record {i}: {lo:#x} >= 2p, {input:?}");
            assert_eq!(
                output.r[4..],
                [0u32; 4],
                "raw record {i}: high words, {input:?}"
            );
            assert_eq!(lo % P, canonical, "raw record {i}: {input:?}");
            assert_eq!(output.carry, 0, "raw record {i}: carry, {input:?}");
        }
    }
}

fn run_raw_probe(inputs: &[PrRawProbeInput]) -> Vec<PrRawProbeOutput> {
    let stream = CudaStream::default();
    let d_inputs = upload_guarded(inputs, &stream);
    let mut d_outputs = alloc_guarded::<PrRawProbeOutput>(inputs.len(), &stream);
    pr_raw_probe(
        &d_inputs[GUARD..GUARD + inputs.len()],
        &mut d_outputs[GUARD..GUARD + inputs.len()],
        &stream,
    )
    .unwrap();
    read_guarded(&d_outputs, inputs.len(), "raw probe output", &stream)
}

#[test]
fn pr_retained_helpers_cpu_parity() {
    let mut rng = seeded_rng();
    let mut inputs = vec![];
    let scalars: Vec<u128> = [0u128, 1, 2, 3, 31, 32, 255, u32::MAX as u128]
        .into_iter()
        .chain((0..64).map(|_| rng.random::<u32>() as u128))
        .collect();
    let mut values = canonical_values();
    values.extend((0..256).map(|_| random_pr(&mut rng)));
    let mut naturals = natural_values();
    naturals.extend([u128::MAX, 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210]);
    naturals.extend((0..64).map(|_| rng.random::<u128>()));
    let mut extracts = vec![(128, 0), (0, 0), (127, 1)];
    for offset in [
        0u32, 1, 17, 31, 32, 33, 63, 64, 65, 95, 96, 97, 100, 112, 127,
    ] {
        for count in [1u32, 31, 32] {
            if offset + count <= 128 {
                extracts.push((offset, count));
            }
        }
    }
    let mut k = 0usize;
    for &a in values.iter() {
        for &s in scalars.iter() {
            let (offset, count) = extracts[k % extracts.len()];
            inputs.push(field_input(
                a,
                a,
                a,
                s,
                naturals[k % naturals.len()],
                (offset, count),
            ));
            k += 1;
        }
    }
    for &n in naturals.iter() {
        for &(offset, count) in extracts.iter() {
            inputs.push(field_input(
                PR::ONE,
                PR::ONE,
                PR::ONE,
                3,
                n,
                (offset, count),
            ));
        }
    }
    check_field_probe(&inputs);

    let mut raw_inputs = vec![];
    for op in OP_ADD_SUB_LIMBS..=OP_REDC_WIDE {
        for &n in raw_op_ns(op) {
            for &width in raw_op_width(op) {
                for &flags in raw_op_flags(op) {
                    for (a, b) in raw_operands(op, n, width, &mut rng) {
                        let a = if width == 4 { w_from(w_lo(&a)) } else { a };
                        let b = if width == 4 { w_from(w_lo(&b)) } else { b };
                        raw_inputs.push(PrRawProbeInput {
                            a,
                            b,
                            op,
                            n,
                            width,
                            flags,
                        });
                    }
                }
            }
        }
    }
    let dirty_high: Vec<PrRawProbeInput> = raw_inputs
        .iter()
        .filter(|input| input.width == 4)
        .step_by(7)
        .map(|input| {
            let mut dirty = *input;
            dirty.a[4..].copy_from_slice(&[0xdead_beef, 0x0bad_f00d, u32::MAX, 1]);
            dirty.b[4..].copy_from_slice(&[0x1234_5678, 0, u32::MAX, 0x8000_0000]);
            dirty
        })
        .collect();
    raw_inputs.extend(dirty_high);
    let invalid = [
        (17, 0, 4, 0),
        (OP_ADD_SUB_LIMBS, 1, 4, 0),
        (OP_ADD_SUB_LIMBS, 0, 4, 4),
        (OP_ADD_SUB_LIMBS, 0, 5, 0),
        (OP_MODULUS, 3, 4, 0),
        (OP_MODULUS, 1, 8, 0),
        (OP_MODULUS_SQUARED, 1, 4, 0),
        (OP_REDUCE, 1, 4, 1),
        (OP_MULTIPLY_RAW, 1, 4, 0),
        (OP_REDC_WIDE_INPLACE, 1, 8, 0),
        (OP_REDC_WIDE, 1, 4, 0),
    ];
    let valid_count = raw_inputs.len();
    for (op, n, width, flags) in invalid {
        raw_inputs.push(PrRawProbeInput {
            a: [7; 8],
            b: [9; 8],
            op,
            n,
            width,
            flags,
        });
    }
    let outputs = run_raw_probe(&raw_inputs);
    for (i, (input, output)) in raw_inputs.iter().zip(outputs.iter()).enumerate() {
        if i < valid_count {
            check_raw_output(input, output, i);
        } else {
            assert_eq!(
                *output,
                PrRawProbeOutput {
                    r: [0; 8],
                    carry: 0,
                    status: RAW_INVALID,
                    _pad: [0; 2]
                },
                "invalid raw record {input:?}"
            );
        }
    }
}

#[test]
fn pr_accessors_shuffle_cpu_parity() {
    const ROWS: usize = 64;
    const STRIDE: usize = 80;
    const COLUMNS: usize = 9;
    let mut rng = seeded_rng();
    let src: Vec<PR> = (0..2 * STRIDE).map(|_| random_pr(&mut rng)).collect();
    let stream = CudaStream::default();
    let d_src = upload_guarded(&src, &stream);
    let mut d_dst = alloc_guarded::<PR>(COLUMNS * STRIDE, &stream);
    pr_access_probe(
        &d_src[GUARD..GUARD + 2 * STRIDE],
        &mut d_dst[GUARD..GUARD + COLUMNS * STRIDE],
        ROWS as u32,
        STRIDE as u32,
        &stream,
    )
    .unwrap();
    let dst = read_guarded(&d_dst, COLUMNS * STRIDE, "access probe dst", &stream);
    let src_back = read_guarded(&d_src, 2 * STRIDE, "access probe src", &stream);
    assert_eq!(bytes_of(&src_back), bytes_of(&src));
    let sentinel = u128::from_ne_bytes([SENTINEL; 16]);
    for column in 0..COLUMNS {
        for row in 0..STRIDE {
            let expected = if row >= ROWS {
                sentinel
            } else {
                match column {
                    0 => src[row].0,
                    1 => src[STRIDE + row].0,
                    2..=6 => src[row ^ (1 << (column - 2))].0,
                    _ => add(src[row], PR::ONE).0,
                }
            };
            assert_eq!(
                dst[column * STRIDE + row].0,
                expected,
                "column {column}, row {row}"
            );
        }
    }
}

fn expected_inverses(values: &[PR]) -> Vec<PR> {
    values
        .iter()
        .map(|v| v.inverse().unwrap_or(PR::ZERO))
        .collect()
}

fn batch_patterns(count: usize, rng: &mut StdRng) -> Vec<(&'static str, Vec<PR>)> {
    let random: Vec<PR> = (0..count).map(|_| random_nonzero_pr(rng)).collect();
    let mut one_nonzero = vec![PR::ZERO; count];
    if count > 0 {
        one_nonzero[count / 2] = random[count / 2];
    }
    let alternating = random
        .iter()
        .enumerate()
        .map(|(i, &v)| if i % 2 == 0 { PR::ZERO } else { v })
        .collect();
    let mut edge_zeros = random.clone();
    if count > 0 {
        edge_zeros[0] = PR::ZERO;
        edge_zeros[count - 1] = PR::ZERO;
    }
    vec![
        ("all zero", vec![PR::ZERO; count]),
        ("one nonzero", one_nonzero),
        ("alternating", alternating),
        ("random", random),
        ("leading and trailing zero", edge_zeros),
    ]
}

#[test]
fn pr_batch_inverse_cpu_parity() {
    let mut rng = seeded_rng();
    let stream = CudaStream::default();
    for count in [0usize, 1, 31, 32, 33, 255, 256, 257, 511, 512, 513, 4096] {
        for (name, values) in batch_patterns(count, &mut rng) {
            let expected = expected_inverses(&values);
            let what = format!("count {count}, {name}");

            let d_input = upload_guarded(&values, &stream);
            let mut d_output = alloc_guarded::<PR>(count, &stream);
            let mut d_prefix = alloc_guarded::<PR>(count, &stream);
            batch_inverse_pr(
                &d_input[GUARD..GUARD + count],
                &mut d_output[GUARD..GUARD + count],
                &mut d_prefix[GUARD..GUARD + count],
                &stream,
            )
            .unwrap();
            assert_eq!(
                read_guarded(&d_output, count, &what, &stream),
                expected,
                "{what}"
            );
            read_guarded(&d_prefix, count, &what, &stream);
            assert_eq!(
                read_guarded(&d_input, count, &what, &stream),
                values,
                "{what}: input"
            );

            let mut d_values = upload_guarded(&values, &stream);
            batch_inverse_pr_in_place(
                &mut d_values[GUARD..GUARD + count],
                &mut d_prefix[GUARD..GUARD + count],
                &stream,
            )
            .unwrap();
            assert_eq!(
                read_guarded(&d_values, count, &what, &stream),
                expected,
                "{what}: in place"
            );
            read_guarded(&d_prefix, count, &what, &stream);

            let mut d_result = alloc_guarded::<PR>(count, &stream);
            inv_pr(
                &d_input[GUARD..GUARD + count],
                &mut d_result[GUARD..GUARD + count],
                &stream,
            )
            .unwrap();
            assert_eq!(
                read_guarded(&d_result, count, &what, &stream),
                expected,
                "{what}: inv_pr"
            );
        }
    }

    let count = 1000;
    let first: Vec<PR> = (0..count).map(|_| random_pr(&mut rng)).collect();
    let second: Vec<PR> = (0..count).map(|_| random_pr(&mut rng)).collect();
    let d_first = upload_guarded(&first, &stream);
    let d_second = upload_guarded(&second, &stream);
    let mut d_out_first = alloc_guarded::<PR>(count, &stream);
    let mut d_out_second = alloc_guarded::<PR>(count, &stream);
    let mut d_prefix = alloc_guarded::<PR>(count, &stream);
    batch_inverse_pr(
        &d_first[GUARD..GUARD + count],
        &mut d_out_first[GUARD..GUARD + count],
        &mut d_prefix[GUARD..GUARD + count],
        &stream,
    )
    .unwrap();
    batch_inverse_pr(
        &d_second[GUARD..GUARD + count],
        &mut d_out_second[GUARD..GUARD + count],
        &mut d_prefix[GUARD..GUARD + count],
        &stream,
    )
    .unwrap();
    assert_eq!(
        read_guarded(&d_out_first, count, "reuse first", &stream),
        expected_inverses(&first)
    );
    assert_eq!(
        read_guarded(&d_out_second, count, "reuse second", &stream),
        expected_inverses(&second)
    );
    read_guarded(&d_prefix, count, "reuse prefix", &stream);
    assert_eq!(
        read_guarded(&d_first, count, "reuse first input", &stream),
        first
    );
    assert_eq!(
        read_guarded(&d_second, count, "reuse second input", &stream),
        second
    );

    let d_three = DeviceAllocation::<PR>::alloc(3).unwrap();
    let mut d_four = DeviceAllocation::<PR>::alloc(4).unwrap();
    assert_eq!(
        panic_message(|| {
            let _ = inv_pr(&d_three, &mut d_four, &stream);
        }),
        "Proth120 inverse length mismatch"
    );
    let huge = u32::MAX as usize + 1;
    let huge_values =
        unsafe { DeviceSlice::<PR>::from_raw_parts(core::ptr::dangling::<PR>(), huge) };
    let huge_result =
        unsafe { DeviceSlice::<PR>::from_raw_parts_mut((1usize << 40) as *mut PR, huge) };
    assert_eq!(
        panic_message(|| {
            let _ = inv_pr(huge_values, huge_result, &stream);
        }),
        "Proth120 inverse count exceeds u32::MAX"
    );
}

#[test]
fn pr_batch_invalid_spans() {
    const E: usize = size_of::<PR>();
    let span = |start: usize, count: usize| (start * E, count * E);
    assert_eq!(check_spans(span(0, 8), span(8, 8), span(16, 8), false), 8);
    assert_eq!(check_spans(span(0, 0), span(0, 0), span(0, 0), false), 0);
    assert_eq!(check_spans(span(16, 8), span(8, 8), span(0, 8), false), 8);
    assert_eq!(check_spans(span(0, 8), span(0, 8), span(8, 8), true), 8);
    let cases: [((usize, usize), (usize, usize), (usize, usize), bool, &str); 9] = [
        (
            span(0, 8),
            span(8, 7),
            span(16, 8),
            false,
            "Proth120 batch inverse length mismatch",
        ),
        (
            span(0, 8),
            span(8, 8),
            span(16, 9),
            false,
            "Proth120 batch inverse length mismatch",
        ),
        (
            (0, (u32::MAX as usize + 1) * E),
            (0, (u32::MAX as usize + 1) * E),
            (0, (u32::MAX as usize + 1) * E),
            false,
            "Proth120 batch inverse count exceeds u32::MAX",
        ),
        (
            (usize::MAX - 4 * E + 1, 4 * E),
            span(0, 4),
            span(4, 4),
            false,
            "Proth120 batch inverse address range overflow",
        ),
        (
            span(0, 8),
            span(0, 8),
            span(16, 8),
            false,
            "Proth120 batch inverse input/output overlap: use in-place API",
        ),
        (
            span(0, 8),
            span(7, 8),
            span(16, 8),
            false,
            "Proth120 batch inverse input/output overlap: use in-place API",
        ),
        (
            span(0, 8),
            span(8, 8),
            span(7, 8),
            false,
            "Proth120 batch inverse prefix overlaps input",
        ),
        (
            span(0, 8),
            span(8, 8),
            span(15, 8),
            false,
            "Proth120 batch inverse prefix overlaps output",
        ),
        (
            span(0, 8),
            span(0, 8),
            span(7, 8),
            true,
            "Proth120 batch inverse prefix overlaps input",
        ),
    ];
    for (input, output, prefix, in_place, message) in cases {
        assert_eq!(
            panic_message(|| {
                check_spans(input, output, prefix, in_place);
            }),
            message,
            "{input:?} {output:?} {prefix:?} {in_place}"
        );
    }
    let empty =
        unsafe { DeviceSlice::<PR>::from_raw_parts(core::ptr::NonNull::dangling().as_ptr(), 0) };
    let empty_output = unsafe {
        DeviceSlice::<PR>::from_raw_parts_mut(core::ptr::NonNull::dangling().as_ptr(), 0)
    };
    let empty_prefix = unsafe {
        DeviceSlice::<PR>::from_raw_parts_mut(core::ptr::NonNull::dangling().as_ptr(), 0)
    };
    let stream = CudaStream::default();
    batch_inverse_pr(empty, empty_output, empty_prefix, &stream).unwrap();
}
