use std::any::TypeId;

use super::*;
use crate::cs::circuit_trait::Circuit;
use crate::cs::circuit_trait::Invariant;
use crate::structured_expr::Expr;
use crate::types::LIMB_WIDTH;
use crate::witness_placer::*;
use field::baby_bear::base::BabyBearField;
use field::PrimeField;

pub fn calculate_pc_next_no_overflows_with_range_checks<F: PrimeField, CS: Circuit<F>>(
    circuit: &mut CS,
    pc: [Variable; REGISTER_SIZE],
    pc_next: [Variable; REGISTER_SIZE],
) {
    // Input invariant: PC % 4 == 0, preserved as:
    // - initial PC is valid % 4
    // - jumps and branches check for alignments

    let [pc_next_low, pc_next_high] = pc_next;

    // range check of both output limbs ensures that there is no overflow/wrap around
    circuit.require_invariant(
        pc_next_low,
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );
    circuit.require_invariant(
        pc_next_high,
        Invariant::RangeChecked {
            width: LIMB_WIDTH as u32,
        },
    );

    let carry = (Expr::<F>::var(pc[0]) + Expr::from(common_constants::PC_STEP as u32)
        - Expr::var(pc_next_low))
        * F::from_u32_unchecked(1 << 16).inverse().unwrap();

    // ensure boolean
    circuit.add_constraint_expr(carry.clone() * (carry.clone() - Expr::one()));

    let pc_high = carry + Expr::var(pc[1]) - Expr::var(pc_next_high);

    // NOTE: we should try to set values before setting constraint as much as possible
    // setting values for overflow flags

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let pc_inc_step = <CS::WitnessPlacer as WitnessTypeSet<F>>::U32::constant(
            common_constants::PC_STEP as u32,
        );
        let pc = placer.get_u32_from_u16_parts(pc);
        let (pc_next_value, _of) = pc.overflowing_add(&pc_inc_step);
        placer.assign_u32_from_u16_parts(pc_next, &pc_next_value);
    };
    circuit.set_values(value_fn);

    circuit.add_constraint_allow_explicit_linear_prevent_optimizations_expr(pc_high);
}

pub(crate) fn montgomery_product_expr<F: PrimeField>(a: Expr<F>, b: Expr<F>) -> Expr<F> {
    if F::IS_MONT_REPR {
        a * b * Expr::<F>::constant(F::from_reduced_raw_repr(1))
    } else {
        a * b
    }
}

/// Witness outputs of the two-field `mop.rr` decomposition (see [`mop_two_field_decompose`]).
///
/// Every field is computed unconditionally on every row; the *consumer* selects the
/// relevant subset per opcode. Values whose meaning is row-conditional are noted below.
pub(crate) struct MopTwoFieldDecomposition<F: PrimeField, W: WitnessTypeSet<F>> {
    /// True Montgomery residue `m = (x·y + is_fma·d·R)·R⁻¹ mod p`, `< p`. Meaningful on
    /// mul/fma rows (feeds the existing `out < p` normalization).
    pub m_int: <W as WitnessTypeSet<F>>::U32,
    /// Committed field variable: the uniform, off-row-safe assignment
    /// `(X·Y + is_fma·D·R̂ + Ĉ·p̂ − q̂·p̂)·R̂⁻¹` evaluated in `F`. Equals `m_int` on
    /// mul/fma rows; equals the (large) forced value `(X·Y + Ĉ·p̂)·R̂⁻¹` off mul-like rows
    /// (because `q̂` is gated to 0 there).
    pub m_field: <W as WitnessTypeSet<F>>::Field,
    /// Quotient `q < 2^35`, gated to 0 off mul-like rows. Low 16 bits.
    pub q_lo16: <W as WitnessTypeSet<F>>::U16,
    /// Quotient bits 16..31.
    pub q_hi16: <W as WitnessTypeSet<F>>::U16,
    /// Quotient bits 32..34 (`q = q_lo16 + q_hi16·2^16 + (t0 + 2·t1 + 4·t2)·2^32`).
    pub q_top_bits: [<W as WitnessTypeSet<F>>::Mask; 3],
    /// addmod reduced output `(x + y) mod p`, `< p`.
    pub out_add: <W as WitnessTypeSet<F>>::U32,
    /// addmod reduction count `k_a = a + b + [x_red + y_red ≥ p] ∈ {0..4}` as 3 bits.
    pub k_add_bits: [<W as WitnessTypeSet<F>>::Mask; 3],
    /// submod reduced output `(x − y) mod p`, `< p`.
    pub out_sub: <W as WitnessTypeSet<F>>::U32,
    /// submod offset count `k_s = 3 + a − b − [x_red < y_red] ∈ {0..5}` as 3 bits.
    pub k_sub_bits: [<W as WitnessTypeSet<F>>::Mask; 3],
}

/// Odd-modulus inverse `p⁻¹ mod 2^64` via Hensel/Newton lifting (requires odd `p`).
///
/// `x₀ = 1` is correct mod 2; each step `x ← x·(2 − p·x)` doubles the number of correct
/// low bits, so 6 iterations reach the full 64 bits.
fn inverse_mod_2_64(p: u64) -> u64 {
    debug_assert_eq!(p & 1, 1, "modular inverse mod 2^64 requires an odd modulus");
    let mut x = 1u64;
    for _ in 0..6 {
        x = x.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(x)));
    }
    debug_assert_eq!(p.wrapping_mul(x), 1, "inverse_mod_2_64 did not converge");
    x
}

/// Reduce a raw word `val < 2^32` modulo `p` (`≈ 2^30.9`) with two conditional
/// subtractions, returning `(val mod p, count)` where `count ∈ {0,1,2}` is the number of
/// subtractions performed. Two subtractions always suffice because `val / p < 2^32/p < 3`.
fn pre_reduce_word<F: PrimeField, W: WitnessTypeSet<F>>(
    val: &<W as WitnessTypeSet<F>>::U32,
    p: &<W as WitnessTypeSet<F>>::U32,
) -> (<W as WitnessTypeSet<F>>::U32, <W as WitnessTypeSet<F>>::U32) {
    // First conditional subtraction.
    let (t1, borrow1) = val.overflowing_sub(p);
    let ge1 = borrow1.negate(); // borrow ⇔ val < p, so `ge = val ≥ p`
    let r1 = <W as WitnessTypeSet<F>>::U32::select(&ge1, &t1, val);
    let mut count = <W as WitnessTypeSet<F>>::U32::from_mask(ge1);
    // Second conditional subtraction.
    let (t2, borrow2) = r1.overflowing_sub(p);
    let ge2 = borrow2.negate();
    let r2 = <W as WitnessTypeSet<F>>::U32::select(&ge2, &t2, &r1);
    count.add_assign(&<W as WitnessTypeSet<F>>::U32::from_mask(ge2));
    (r2, count)
}

/// Witness generation for the two-field `mop.rr` path (circuit field `F` ≠ mop field
/// `MopF`, the latter assumed to be a `≈2^31` prime field in Montgomery form — BabyBear).
///
/// Given register words `x, y, d` (raw, `< 2^32`, NOT necessarily `< p`) and the row flags
/// `is_fma` / `is_mul_like`, computes — over the u32 placer API plus `Field::from_integer`,
/// with NO `u64`/`U64` placer type — the witness pieces the constraints will bind:
///
/// * `m_int` — the true residue `m = (x·y + is_fma·d·R)·R⁻¹ mod p` via input pre-reduction
///   + one canonical word Montgomery REDC (+ one canonical addmod for fma);
/// * `q` (`< 2^35`) — the exact quotient of `N = x·y + is_fma·d·R + C·p − m_int·R = q·p`,
///   recovered as `N mod 2^64` times `p⁻¹ mod 2^64` (valid mod `2^64` since `q < 2^35`),
///   split into `(q_lo16, q_hi16, t0, t1, t2)` and gated to 0 off mul-like rows;
/// * `m_field` — the uniform, off-row-safe field assignment
///   `(X·Y + is_fma·D·R̂ + Ĉ·p̂ − q̂·p̂)·R̂⁻¹` (equals `m_int` on mul-like rows);
/// * `out`/`k` for addmod and submod — reduce-then-count (no wide divmod).
pub(crate) fn mop_two_field_decompose<F: PrimeField, MopF: PrimeField, W: WitnessTypeSet<F>>(
    x: &<W as WitnessTypeSet<F>>::U32,
    y: &<W as WitnessTypeSet<F>>::U32,
    d: &<W as WitnessTypeSet<F>>::U32,
    is_fma: &<W as WitnessTypeSet<F>>::Mask,
    is_mul_like: &<W as WitnessTypeSet<F>>::Mask,
) -> MopTwoFieldDecomposition<F, W> {
    assert_eq!(
        TypeId::of::<MopF>(),
        TypeId::of::<BabyBearField>(),
        "we assume the mop.rr field is always BabyBear"
    );

    type U32Of<F, W> = <W as WitnessTypeSet<F>>::U32;
    type FieldOf<F, W> = <W as WitnessTypeSet<F>>::Field;

    // ---- constants (single source of truth: MopF's modulus and C = R = 2^32) ----
    let p_u32 = MopF::CHARACTERISTICS_U32;
    let pinv64 = inverse_mod_2_64(p_u32 as u64);
    let p_prime = (pinv64 as u32).wrapping_neg(); // −p⁻¹ mod 2^32
    let pinv_lo = pinv64 as u32;
    let pinv_hi = (pinv64 >> 32) as u32;

    let p_const = U32Of::<F, W>::constant(p_u32);
    let p_prime_const = U32Of::<F, W>::constant(p_prime);
    let pinv_lo_const = U32Of::<F, W>::constant(pinv_lo);
    let pinv_hi_const = U32Of::<F, W>::constant(pinv_hi);
    let zero_u32 = U32Of::<F, W>::constant(0);

    // F constants: R̂ = 2^32, p̂ = p, Ĉ·p̂ = C·p = 2^32·p, R̂⁻¹.
    let r_hat = F::from_u128_with_reduction(1u128 << 32);
    let p_hat = F::from_u32_with_reduction(p_u32);
    let cp_hat = F::from_u128_with_reduction((1u128 << 32) * (p_u32 as u128));
    let r_inv = r_hat
        .inverse()
        .expect("R must be invertible in the circuit field");
    let r_hat_f = FieldOf::<F, W>::constant(r_hat);
    let p_hat_f = FieldOf::<F, W>::constant(p_hat);
    let cp_hat_f = FieldOf::<F, W>::constant(cp_hat);
    let r_inv_f = FieldOf::<F, W>::constant(r_inv);

    // ---- pre-reduce inputs (shared by the mul/fma REDC and the add/sub paths) ----
    let (x_red, a) = pre_reduce_word::<F, W>(x, &p_const);
    let (y_red, b) = pre_reduce_word::<F, W>(y, &p_const);
    let (d_red, _delta) = pre_reduce_word::<F, W>(d, &p_const);

    // ---- m_int: canonical word Montgomery REDC of (x_red · y_red), then fma addmod ----
    // T = x_red·y_red < p² < p·R  ⇒  standard single-word REDC applies.
    let (t_lo, t_hi) = x_red.split_widening_product(&y_red);
    // mm = (T mod R)·p' mod R.
    let mm = t_lo.wrapping_product(&p_prime_const);
    // mp = mm·p.
    let (mp_lo, mp_hi) = mm.split_widening_product(&p_const);
    // Low word of T + mm·p is ≡ 0 mod R by REDC; capture only the carry-out.
    let (_low, redc_carry) = t_lo.overflowing_add(&mp_lo);
    // High word = (T + mm·p)/R < 2p < 2^32, so this addition does not overflow u32.
    let (redc_hi, _of) = t_hi.overflowing_add_with_carry(&mp_hi, &redc_carry);
    // One conditional subtraction to land in [0, p).
    let (redc_sub, redc_borrow) = redc_hi.overflowing_sub(&p_const);
    let redc_ge = redc_borrow.negate();
    let m_mul = U32Of::<F, W>::select(&redc_ge, &redc_sub, &redc_hi);
    // fma: (m_mul + d_red) mod p — one more conditional subtraction (m_mul, d_red < p).
    let (fma_sum, _of) = m_mul.overflowing_add(&d_red);
    let (fma_sub, fma_borrow) = fma_sum.overflowing_sub(&p_const);
    let fma_ge = fma_borrow.negate();
    let m_fma = U32Of::<F, W>::select(&fma_ge, &fma_sub, &fma_sum);
    let m_int = U32Of::<F, W>::select(is_fma, &m_fma, &m_mul);

    // ---- q: exact division N/p via (N mod 2^64)·(p⁻¹ mod 2^64) mod 2^64 ----
    // N = x·y + is_fma·d·R + C·p − m_int·R (RAW words). Because C = R = 2^32, both
    // `d·R`, `C·p = 2^32·p` and `m_int·R` contribute only to the high 32-bit limb, so
    // the low limb of `N mod 2^64` is exactly the low word of `x·y`.
    let (xy_lo, xy_hi) = x.split_widening_product(y);
    let n_lo = xy_lo;
    let mut n_hi = xy_hi;
    // n_hi accumulates is_fma·d + p − m_int: each of d·R, C·p = 2^32·p and m_int·R shifts
    // by R = 2^32 into the high limb (the +p realises C·p), leaving the low limb = x·y's.
    let d_term = U32Of::<F, W>::select(is_fma, d, &zero_u32);
    n_hi.add_assign(&d_term);
    n_hi.add_assign(&p_const);
    n_hi.sub_assign(&m_int);
    // q = (n_lo, n_hi) · (pinv_lo, pinv_hi) mod 2^64, low 64 bits only (3 u32 mults).
    let (q_ll_lo, q_ll_hi) = n_lo.split_widening_product(&pinv_lo_const);
    let q_cross_lo = n_lo.wrapping_product(&pinv_hi_const);
    let q_cross_hi = n_hi.wrapping_product(&pinv_lo_const);
    let q_lo = q_ll_lo;
    let mut q_hi = q_ll_hi;
    q_hi.add_assign(&q_cross_lo);
    q_hi.add_assign(&q_cross_hi); // q_hi < 8 (since q < 2^35)

    // Gate q to 0 off mul-like rows, matching the fully `is_mul_like`-masked q̂ in the mul
    // relation (`… − q̂·p̂ − …` with q̂ = (q_lo16 + q_hi16·2^16 + k·2^32)·is_mul_like): the
    // witness q̂ collapses to 0 on non-mul rows exactly as the constraint does — there is no
    // longer a separate DoF gate.
    let q_lo_g = U32Of::<F, W>::select(is_mul_like, &q_lo, &zero_u32);
    let q_hi_g = U32Of::<F, W>::select(is_mul_like, &q_hi, &zero_u32);
    let q_lo16 = q_lo_g.truncate();
    let q_hi16 = q_lo_g.shr(16).truncate();
    let q_top_bits = [q_hi_g.get_bit(0), q_hi_g.get_bit(1), q_hi_g.get_bit(2)];

    // ---- m_field: uniform field formula (equals m_int on mul-like rows) ----
    // q̂ reconstructed from the gated limbs, so it is 0 off mul-like rows.
    let mut q_hat = FieldOf::<F, W>::from_integer(q_lo_g);
    let q_hi_f = FieldOf::<F, W>::from_integer(q_hi_g);
    q_hat.add_assign_product(&q_hi_f, &r_hat_f); // q̂ = q_lo_g + q_hi_g·R̂
    let mut m_field = FieldOf::<F, W>::from_integer(x.clone());
    let y_f = FieldOf::<F, W>::from_integer(y.clone());
    m_field.mul_assign(&y_f); // X·Y
    let mut d_r = FieldOf::<F, W>::from_integer(d.clone());
    d_r.mul_assign(&r_hat_f); // D·R̂
    m_field.add_assign_masked(is_fma, &d_r); // + is_fma·D·R̂
    m_field.add_assign(&cp_hat_f); // + Ĉ·p̂
    let mut q_p = q_hat;
    q_p.mul_assign(&p_hat_f);
    m_field.sub_assign(&q_p); // − q̂·p̂
    m_field.mul_assign(&r_inv_f); // · R̂⁻¹

    // ---- addmod: out = (x + y) mod p, k = a + b + [x_red + y_red ≥ p] ----
    let (add_sum, _of) = x_red.overflowing_add(&y_red); // < 2p < 2^32, no overflow
    let (add_sub, add_borrow) = add_sum.overflowing_sub(&p_const);
    let add_ge = add_borrow.negate(); // x_red + y_red ≥ p
    let out_add = U32Of::<F, W>::select(&add_ge, &add_sub, &add_sum);
    let mut k_add = a.clone();
    k_add.add_assign(&b);
    k_add.add_assign(&U32Of::<F, W>::from_mask(add_ge));
    let k_add_bits = [k_add.get_bit(0), k_add.get_bit(1), k_add.get_bit(2)];

    // ---- submod: out = (x − y) mod p, k = 3 + a − b − [x_red < y_red] ----
    let (sub_diff, sub_borrow) = x_red.overflowing_sub(&y_red);
    let (sub_wrap, _of) = sub_diff.overflowing_add(&p_const); // (x_red − y_red + p) mod 2^32
    let out_sub = U32Of::<F, W>::select(&sub_borrow, &sub_wrap, &sub_diff);
    let mut k_sub = U32Of::<F, W>::constant(3);
    k_sub.add_assign(&a);
    k_sub.sub_assign(&b);
    k_sub.sub_assign(&U32Of::<F, W>::from_mask(sub_borrow));
    let k_sub_bits = [k_sub.get_bit(0), k_sub.get_bit(1), k_sub.get_bit(2)];

    MopTwoFieldDecomposition {
        m_int,
        m_field,
        q_lo16,
        q_hi16,
        q_top_bits,
        out_add,
        k_add_bits,
        out_sub,
        k_sub_bits,
    }
}

pub(crate) fn update_intermediate_carry_value<
    F: PrimeField,
    W: WitnessPlacer<F>,
    const IS_SUB: bool,
>(
    intermediate_carry: &mut <W as WitnessTypeSet<F>>::Mask,
    flag: &<W as WitnessTypeSet<F>>::Mask,
    a: &<W as WitnessTypeSet<F>>::U16,
    b: &<W as WitnessTypeSet<F>>::U16,
    imm_for_b: Option<&<W as WitnessTypeSet<F>>::U16>,
) {
    if IS_SUB {
        let (tmp, of0) = a.overflowing_sub(b);
        if let Some(imm_for_b) = imm_for_b {
            let (_, of1) = tmp.overflowing_sub(imm_for_b);
            let of = of0.or(&of1);
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of, &*intermediate_carry);
        } else {
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of0, &*intermediate_carry);
        }
    } else {
        let (tmp, of0) = a.overflowing_add(b);
        if let Some(imm_for_b) = imm_for_b {
            let (_, of1) = tmp.overflowing_add(imm_for_b);
            let of = of0.or(&of1);
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of, &*intermediate_carry);
        } else {
            *intermediate_carry =
                <W as WitnessTypeSet<F>>::Mask::select(flag, &of0, &*intermediate_carry);
        }
    }
}

#[cfg(test)]
mod mop_two_field_decompose_tests {
    use super::*;
    use crate::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use field::baby_bear::base::BabyBearField;
    use field::proth120::Proth120;
    use field::Field;

    type F = Proth120;
    type MopF = BabyBearField;
    type W = ScalarWitnessTypeSet<Proth120, false>;

    const P: u64 = 0x78000001; // BabyBear prime (2013265921)
    const R: u64 = 1 << 32;
    const C: u64 = 1 << 32; // offset keeping q ≥ 0
    const RR: u32 = (R % P) as u32; // R mod p = 268435454 (Montgomery repr of 1's neighbour)

    fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
        let mut acc = 1u128;
        base %= modulus;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc * base % modulus;
            }
            base = base * base % modulus;
            exp >>= 1;
        }
        acc
    }

    /// Modular inverse for a prime modulus via Fermat's little theorem.
    fn mod_inv_prime(a: u128, modulus: u128) -> u128 {
        mod_pow(a, modulus - 2, modulus)
    }

    /// `m = (x·y + is_fma·d·R)·R⁻¹ mod p`, computed on raw words (mod-p reduce then
    /// multiply by `R⁻¹ mod p`).
    fn oracle_m_int(x: u64, y: u64, d: u64, is_fma: bool) -> u64 {
        let p = P as u128;
        let r_inv = mod_inv_prime(R as u128 % p, p);
        let mut m = (x as u128 % p) * (y as u128 % p) % p;
        m = m * r_inv % p;
        if is_fma {
            m = (m + d as u128 % p) % p;
        }
        m as u64
    }

    fn oracle_q(x: u64, y: u64, d: u64, is_fma: bool, m: u64) -> u64 {
        let p = P as u128;
        let n = (x as u128) * (y as u128)
            + if is_fma { (d as u128) * (R as u128) } else { 0 }
            + (C as u128) * p
            - (m as u128) * (R as u128);
        assert_eq!(n % p, 0, "N must be divisible by p");
        let q = n / p;
        assert!(q < (1u128 << 35), "q must fit in 35 bits, got {q}");
        q as u64
    }

    fn oracle_add(x: u64, y: u64) -> (u64, u64) {
        let p = P as u128;
        let s = x as u128 + y as u128;
        ((s % p) as u64, (s / p) as u64)
    }

    fn oracle_sub(x: u64, y: u64) -> (u64, u64) {
        let p = P as i128;
        let out = ((x as i128 - y as i128) % p + p) % p;
        let val = x as i128 - y as i128 + 3 * p;
        let k = (val - out) / p;
        (out as u64, k as u64)
    }

    struct Decoded {
        m_int: u32,
        m_field: Proth120,
        q: u64,
        q_top: [bool; 3],
        out_add: u32,
        k_add: u64,
        out_sub: u32,
        k_sub: u64,
    }

    fn bits3(b: [bool; 3]) -> u64 {
        b[0] as u64 + 2 * (b[1] as u64) + 4 * (b[2] as u64)
    }

    fn run(x: u32, y: u32, d: u32, is_fma: bool, is_mul_like: bool) -> Decoded {
        let r = mop_two_field_decompose::<F, MopF, W>(&x, &y, &d, &is_fma, &is_mul_like);
        Decoded {
            m_int: r.m_int,
            m_field: r.m_field,
            q: r.q_lo16 as u64 + ((r.q_hi16 as u64) << 16) + (bits3(r.q_top_bits) << 32),
            q_top: r.q_top_bits,
            out_add: r.out_add,
            k_add: bits3(r.k_add_bits),
            out_sub: r.out_sub,
            k_sub: bits3(r.k_sub_bits),
        }
    }

    #[test]
    fn oracle_known_values() {
        assert_eq!(oracle_m_int(1, 1, 0, false), 0x3840_0000, "R⁻¹ mod p");
        assert_eq!(
            oracle_m_int(RR as u64, RR as u64, 0, false),
            RR as u64,
            "mont(R,R)=R"
        );
        assert_eq!(
            oracle_m_int(RR as u64, RR as u64, RR as u64, true),
            (2 * (R % P)) % P,
            "fma R,R,R = 2R mod p"
        );
        assert_eq!(oracle_add(P - 1, 1), (0, 1));
        assert_eq!(oracle_add((1 << 32) - 1, (1 << 32) - 1).1, 4);
        assert_eq!(oracle_sub(0, 1).0, P - 1);
        assert_eq!(oracle_sub((1 << 32) - 1, 0).1, 5);
        assert_eq!(oracle_sub(0, (1 << 32) - 1).1, 0);
    }

    #[test]
    fn helper_matches_oracle_mul_fma() {
        // (x, y, d, is_fma)
        let vectors: [(u32, u32, u32, bool); 6] = [
            (RR, RR, 0, false),                   // raw x=y=R  ⇒ m_int = R
            (1, 1, 0, false),                     // x=y=1      ⇒ m_int = R⁻¹ mod p
            (u32::MAX, u32::MAX, 0, false),       // raw 2^32−1 (needs input pre-reduction)
            (u32::MAX, u32::MAX, u32::MAX, true), // fma 2^32−1 (multiple subtractions)
            (0, 0, 0, false),                     // x=y=0      ⇒ m_int = 0
            (RR, RR, RR, true),                   // fma R,R,R  ⇒ m_int = 2R mod p
        ];
        for (x, y, d, is_fma) in vectors {
            let m = oracle_m_int(x as u64, y as u64, d as u64, is_fma);
            let q = oracle_q(x as u64, y as u64, d as u64, is_fma, m);
            let dec = run(x, y, d, is_fma, true);
            assert_eq!(
                dec.m_int as u64, m,
                "m_int mismatch for x={x} y={y} d={d} fma={is_fma}"
            );
            assert_eq!(dec.q, q, "q mismatch for x={x} y={y} d={d} fma={is_fma}");
            assert!(dec.q < (1 << 35), "q must be < 2^35");
            assert!(bits3(dec.q_top) < 8, "top limb < 8");
            // On mul-like rows the uniform field formula must coincide with the residue.
            assert_eq!(
                dec.m_field,
                Proth120::from_u32_with_reduction(m as u32),
                "m_field must equal F(m_int) on mul-like rows for x={x} y={y}"
            );
        }
    }

    #[test]
    fn helper_matches_oracle_add_sub() {
        // (x, y)
        let vectors: [(u32, u32); 6] = [
            (P as u32 - 1, 1),    // addmod ⇒ out=0, k=1
            (u32::MAX, u32::MAX), // addmod ⇒ k=4
            (0, 1),               // submod ⇒ out=p−1, k=2
            (u32::MAX, 0),        // submod extreme ⇒ k=5
            (0, u32::MAX),        // submod extreme ⇒ k=0
            (12345678, 87654321), // generic in-range
        ];
        for (x, y) in vectors {
            let (oa, ka) = oracle_add(x as u64, y as u64);
            let (os, ks) = oracle_sub(x as u64, y as u64);
            // Flags irrelevant for the add/sub outputs; use a plain (non-mul) row.
            let dec = run(x, y, 0, false, false);
            assert_eq!(dec.out_add as u64, oa, "out_add mismatch x={x} y={y}");
            assert_eq!(dec.k_add, ka, "k_add mismatch x={x} y={y}");
            assert!(dec.k_add <= 4, "k_add ∈ {{0..4}}");
            assert_eq!(dec.out_sub as u64, os, "out_sub mismatch x={x} y={y}");
            assert_eq!(dec.k_sub, ks, "k_sub mismatch x={x} y={y}");
            assert!(dec.k_sub <= 5, "k_sub ∈ {{0..5}}");
        }
    }

    #[test]
    fn q_and_m_field_gated_off_mul_rows() {
        // Off mul-like rows: q pieces are 0, and m_field is the large forced value
        // (x·y + C·p)·R⁻¹ — NOT the reduced residue.
        let dec = run(RR, RR, 0, false, false);
        assert_eq!(dec.q, 0, "q must be gated to 0 off mul-like rows");
        assert_eq!(dec.q_top, [false, false, false]);

        // Independently recompute the off-row formula in F (UFCS to disambiguate the
        // `field::Field` methods from the witness-placer trait's same-named methods).
        let mut expected = Proth120::from_u32_with_reduction(RR);
        let y_f = Proth120::from_u32_with_reduction(RR);
        Field::mul_assign(&mut expected, &y_f);
        let cp = Proth120::from_u128_with_reduction((C as u128) * (P as u128));
        Field::add_assign(&mut expected, &cp);
        let r_hat = Proth120::from_u128_with_reduction(R as u128);
        let r_inv = Field::inverse(&r_hat).unwrap();
        Field::mul_assign(&mut expected, &r_inv);
        assert_eq!(
            dec.m_field, expected,
            "off-row m_field must be the large forced value"
        );
        assert_ne!(
            dec.m_field,
            Proth120::from_u32_with_reduction(RR),
            "off-row m_field must differ from the on-row residue (gating actually applied)"
        );
    }

    #[test]
    fn ssa_transpiles_including_off_row_path() {
        use crate::cs::circuit_trait::Circuit;
        use crate::gkr_compiler::dump_ssa_witness_eval_form;
        use crate::oracle::Placeholder;
        use crate::witness_placer::graph_description::WitnessGraphCreator;

        let ssa = dump_ssa_witness_eval_form::<Proth120>(&|_cs| {}, &|cs| {
            let m_field_v = cs.add_variable();
            let m_int_v = [cs.add_variable(), cs.add_variable()];
            let q_lo16_v = cs.add_variable();
            let q_hi16_v = cs.add_variable();
            let q_top_v = [cs.add_variable(), cs.add_variable(), cs.add_variable()];
            let out_add_v = [cs.add_variable(), cs.add_variable()];
            let k_add_v = [cs.add_variable(), cs.add_variable(), cs.add_variable()];
            let out_sub_v = [cs.add_variable(), cs.add_variable()];
            let k_sub_v = [cs.add_variable(), cs.add_variable(), cs.add_variable()];

            cs.set_values(move |placer: &mut WitnessGraphCreator<Proth120>| {
                // Symbolic inputs via oracle leaves — is_mul_like/is_fma are free
                // Booleans, so BOTH the mul path and the off-row (plain-ADD) path of
                // the m_field formula are present in the emitted graph.
                let x = placer.get_oracle_u32(Placeholder::ShuffleRamReadValue(0));
                let y = placer.get_oracle_u32(Placeholder::ShuffleRamReadValue(1));
                let d = placer.get_oracle_u32(Placeholder::ShuffleRamReadValue(2));
                let is_fma = placer.get_oracle_boolean(Placeholder::ShuffleRamIsRegisterAccess(0));
                let is_mul_like =
                    placer.get_oracle_boolean(Placeholder::ShuffleRamIsRegisterAccess(1));

                let dec = mop_two_field_decompose::<
                    Proth120,
                    BabyBearField,
                    WitnessGraphCreator<Proth120>,
                >(&x, &y, &d, &is_fma, &is_mul_like);

                placer.assign_field(m_field_v, &dec.m_field);
                placer.assign_u32_from_u16_parts(m_int_v, &dec.m_int);
                placer.assign_u16(q_lo16_v, &dec.q_lo16);
                placer.assign_u16(q_hi16_v, &dec.q_hi16);
                for (v, b) in q_top_v.iter().zip(dec.q_top_bits.iter()) {
                    placer.assign_mask(*v, b);
                }
                placer.assign_u32_from_u16_parts(out_add_v, &dec.out_add);
                for (v, b) in k_add_v.iter().zip(dec.k_add_bits.iter()) {
                    placer.assign_mask(*v, b);
                }
                placer.assign_u32_from_u16_parts(out_sub_v, &dec.out_sub);
                for (v, b) in k_sub_v.iter().zip(dec.k_sub_bits.iter()) {
                    placer.assign_mask(*v, b);
                }
            });
        });

        assert!(
            !ssa.is_empty(),
            "SSA forms must be produced (helper transpiled)"
        );
    }
}
