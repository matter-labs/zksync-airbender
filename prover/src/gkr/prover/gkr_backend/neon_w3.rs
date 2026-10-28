//! The NEON backend's own window-3 pass kernels (BabyBear / Ext4).
//!
//! Same per-row semantics as the `lsb_bench` window-3 kernels
//! (`lsb_soa_full_parallel` for the INITIAL pass over the original base/ext
//! inputs, `lsb_soa_ext_pass_parallel` for the CONTINUING passes over the
//! folded all-ext tables): 7 SoA groups of 4 cells = 8 binary cells in
//! groups 0..2 + 19 infinity cells + 1 pad; forms, factored products,
//! flattened rest steps, scalar eq weight per row. Two differences:
//!
//! * **Register-resident lazy accumulation.** The term list is swept once
//!   per group range (3 + 2 + 2 groups for the initial pass, 2 + 2 + 2 + 1
//!   for the all-ext continuing pass), each sweep keeping its
//!   `[groups][4 limbs] x (lo, hi)` u64 accumulators in NEON registers, so a
//!   term costs its grid loads and its multiplies, with no accumulator
//!   loads/stores; the `R*P` conditional subtraction that bounds the u64
//!   lanes (every second raw product, as in the memory-resident kernels)
//!   becomes register ALU work.
//! * **Lazy extension products.** `a (x) b` for two variable ext cells is
//!   formed from 16 raw u64 cross products (b's limbs 1..3 pre-scaled by 11,
//!   each output limb `< 4 P^2`) and ONE REDC per limb instead of the 19
//!   canonical `mont_mul4` of `soa_ext_mul`; the constant coefficient of every
//!   ext term is applied by lane-indexed `umlal`s from two broadcast vectors
//!   (`c` and `11 c`) straight into the lazy accumulators, never by a second
//!   ext multiply.
//!
//! * **Operand-grouped terms.** The quadratic terms are regrouped by shared
//!   operand once per layer (`GroupedProgram`): `sum_k c_k a b_k` is evaluated
//!   as `a * sum_k c_k b_k`, one product per group instead of one per term
//!   (the inner sums are coefficient multiply-accumulates). On the unified
//!   extended machine 268 of layer 0's 289 factored products share an operand.
//!
//! * **Vector grid extrapolation.** The 19 infinity cells of a window-3 grid
//!   are gathered differences of the 8 taps (`vqtbl3q_u8` gathers + lane-wise
//!   modular subtracts for base slots, whole-`Ext4` vector subtracts for ext
//!   slots) instead of 19 scalar branchy subtractions.
//!
//! Everything is exact modular arithmetic finished by one canonical REDC
//! per cell, so the results are bit-identical to the lsb_bench kernels
//! (asserted by the `pressure_probe` A/B and by the proof fixtures).

use super::super::sumcheck_loop::windowed_mode::lsb_bench::{
    apply_ext_form_op, apply_ext_form_op_first, apply_form_op, apply_form_op_first, finish_soa_acc,
    W3_INF,
};
use super::super::sumcheck_loop::windowed_mode::neon;
use super::super::sumcheck_loop::windowed_mode::program::{FormRef, ProgramStep};
use super::super::sumcheck_loop::OwnedSoaProgram;
use crate::gkr::PAR_THRESHOLD;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use ::field::{Field, PrimeField};
use core::arch::aarch64::*;
use worker::Worker;

const P: u32 = 0x78000001;
const K: u32 = 0x77ffffff; // -P^{-1} mod 2^32
const RP: u64 = (P as u64) << 32;
const NG: usize = 7;
const NBIN: usize = 2;
/// base grid stride in u32 (28 cells)
const BS: usize = 4 * NG;
/// ext grid / SoA buffer stride in u32 (28 cells x 4 limbs)
const ES: usize = 16 * NG;

/// One SoA limb's lazy u64 accumulator over 4 cells, register-resident.
#[derive(Clone, Copy)]
struct Acc {
    lo: uint64x2_t,
    hi: uint64x2_t,
}

impl Acc {
    #[inline(always)]
    unsafe fn zero() -> Self {
        Acc {
            lo: vdupq_n_u64(0),
            hi: vdupq_n_u64(0),
        }
    }

    /// `self += t * c[L]` over the 4 cells (raw 64-bit products).
    #[inline(always)]
    unsafe fn mla_lane<const L: i32>(&mut self, t: uint32x4_t, c: uint32x4_t) {
        self.lo = vmlal_laneq_u32::<L>(self.lo, vget_low_u32(t), c);
        self.hi = vmlal_high_laneq_u32::<L>(self.hi, t, c);
    }

    /// `self += a * b` cellwise (raw 64-bit products).
    #[inline(always)]
    unsafe fn mla(&mut self, a: uint32x4_t, b: uint32x4_t) {
        self.lo = vmlal_u32(self.lo, vget_low_u32(a), vget_low_u32(b));
        self.hi = vmlal_high_u32(self.hi, a, b);
    }

    #[inline(always)]
    unsafe fn condsub(&mut self) {
        let rp = vdupq_n_u64(RP);
        self.lo = vsubq_u64(self.lo, vandq_u64(vcgeq_u64(self.lo, rp), rp));
        self.hi = vsubq_u64(self.hi, vandq_u64(vcgeq_u64(self.hi, rp), rp));
    }

    /// Canonical REDC of the accumulated sum (same arithmetic as
    /// `neon::soa_lazy_finalize`): valid for sums `< 2 R P`, i.e. `< R P`
    /// after the leading condsub, which every call site guarantees (at most
    /// 4 raw `< P^2` products since the last condsub).
    #[inline(always)]
    unsafe fn redc(mut self) -> uint32x4_t {
        self.condsub();
        let p2 = vdup_n_u32(P);
        let k2 = vdup_n_u32(K);
        let m_lo = vmul_u32(vmovn_u64(self.lo), k2);
        let m_hi = vmul_u32(vmovn_u64(self.hi), k2);
        let lo = vmlal_u32(self.lo, m_lo, p2);
        let hi = vmlal_u32(self.hi, m_hi, p2);
        let r = vcombine_u32(vshrn_n_u64::<32>(lo), vshrn_n_u64::<32>(hi));
        vminq_u32(r, vsubq_u32(r, vdupq_n_u32(P)))
    }
}

/// `acc[l] += t * c[l]` for the 4 coefficient limbs (base value `t`).
#[inline(always)]
unsafe fn mla4(acc: &mut [Acc; 4], t: uint32x4_t, c: uint32x4_t) {
    acc[0].mla_lane::<0>(t, c);
    acc[1].mla_lane::<1>(t, c);
    acc[2].mla_lane::<2>(t, c);
    acc[3].mla_lane::<3>(t, c);
}

#[inline(always)]
unsafe fn condsub4(acc: &mut [Acc; 4]) {
    for l in 0..4 {
        acc[l].condsub();
    }
}

/// A constant ext coefficient as the two broadcast vectors the lane-indexed
/// table multiply needs: `c = (c0, c1, c2, c3)` and `cs = 11 c` (canonical).
#[derive(Clone, Copy)]
struct Coeff {
    c: uint32x4_t,
    cs: uint32x4_t,
}

impl Coeff {
    #[inline(always)]
    unsafe fn new(v: &BabyBearExt4) -> Self {
        let l: [u32; 4] = core::mem::transmute(*v);
        let e11 = BabyBearField::new(11);
        let s: [u32; 4] = core::array::from_fn(|i| {
            let mut t = BabyBearField::from_raw_u32(l[i]);
            t.mul_assign(&e11);
            t.raw_u32_value()
        });
        Coeff {
            c: vld1q_u32(l.as_ptr()),
            cs: vld1q_u32(s.as_ptr()),
        }
    }
}

/// `acc += coeff (x) v` for a canonical SoA ext cell group `v` (4 limb
/// vectors), fully lazy: the flat quartic table of `BabyBearExt4` with the
/// coefficient fixed —
/// `out0 = c0 v0 + 11c1 v1 + 11c3 v2 + 11c2 v3`,
/// `out1 = c1 v0 +   c0 v1 +   c2 v2 + 11c3 v3`,
/// `out2 = c2 v0 + 11c3 v1 +   c0 v2 + 11c1 v3`,
/// `out3 = c3 v0 +   c2 v1 +   c1 v2 +   c0 v3` —
/// as 4 raw products per limb with a condsub after every second one.
/// Requires `acc < R P` on entry; leaves `acc < R P`.
#[inline(always)]
unsafe fn table_mla4(acc: &mut [Acc; 4], v: &[uint32x4_t; 4], k: &Coeff) {
    acc[0].mla_lane::<0>(v[0], k.c);
    acc[0].mla_lane::<1>(v[1], k.cs);
    acc[1].mla_lane::<1>(v[0], k.c);
    acc[1].mla_lane::<0>(v[1], k.c);
    acc[2].mla_lane::<2>(v[0], k.c);
    acc[2].mla_lane::<3>(v[1], k.cs);
    acc[3].mla_lane::<3>(v[0], k.c);
    acc[3].mla_lane::<2>(v[1], k.c);
    condsub4(acc);
    acc[0].mla_lane::<3>(v[2], k.cs);
    acc[0].mla_lane::<2>(v[3], k.cs);
    acc[1].mla_lane::<2>(v[2], k.c);
    acc[1].mla_lane::<3>(v[3], k.cs);
    acc[2].mla_lane::<0>(v[2], k.c);
    acc[2].mla_lane::<1>(v[3], k.cs);
    acc[3].mla_lane::<1>(v[2], k.c);
    acc[3].mla_lane::<0>(v[3], k.c);
    condsub4(acc);
}

/// Lazy cellwise `a (x) b` of two canonical SoA ext cell groups: `b`'s limbs
/// 1..3 pre-scaled by 11 (three canonical products), each output limb the
/// u64 sum of its four raw cross products (`< 4 P^2`), ONE REDC per limb.
/// Same values as `neon::soa_ext_mul` (7 canonical multiplies instead of 19).
#[inline(always)]
unsafe fn ext_mul_lazy(
    a: &[uint32x4_t; 4],
    b: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) -> [uint32x4_t; 4] {
    let b1s = neon::mont_mul4(b[1], r11v);
    let b2s = neon::mont_mul4(b[2], r11v);
    let b3s = neon::mont_mul4(b[3], r11v);
    // out0 = a0 b0 + 11 a1 b1 + 11 a2 b3 + 11 a3 b2
    let mut l0 = Acc::zero();
    l0.mla(a[0], b[0]);
    l0.mla(a[1], b1s);
    l0.mla(a[2], b3s);
    l0.mla(a[3], b2s);
    // out1 = a0 b1 + a1 b0 + a2 b2 + 11 a3 b3
    let mut l1 = Acc::zero();
    l1.mla(a[0], b[1]);
    l1.mla(a[1], b[0]);
    l1.mla(a[2], b[2]);
    l1.mla(a[3], b3s);
    // out2 = a0 b2 + a2 b0 + 11 a1 b3 + 11 a3 b1
    let mut l2 = Acc::zero();
    l2.mla(a[0], b[2]);
    l2.mla(a[2], b[0]);
    l2.mla(a[1], b3s);
    l2.mla(a[3], b1s);
    // out3 = a0 b3 + a1 b2 + a2 b1 + a3 b0
    let mut l3 = Acc::zero();
    l3.mla(a[0], b[3]);
    l3.mla(a[1], b[2]);
    l3.mla(a[2], b[1]);
    l3.mla(a[3], b[0]);
    [l0.redc(), l1.redc(), l2.redc(), l3.redc()]
}

#[inline(always)]
unsafe fn load_cell(p: *const u32) -> [uint32x4_t; 4] {
    core::array::from_fn(|l| vld1q_u32(p.add(4 * l)))
}

#[inline(always)]
unsafe fn coeff_vec(c: &BabyBearExt4) -> uint32x4_t {
    vld1q_u32(c as *const BabyBearExt4 as *const u32)
}

/// Montgomery bookkeeping of the lazy accumulators: every raw product of two
/// Montgomery-form values is `R^2`-scaled, and the final REDC brings the sum
/// back to Montgomery form. A group's `pivot (x) inner` is therefore added as
/// RAW products as well — base pivot x canonical inner limbs directly
/// (`umlal`), an ext product's canonical result times `R mod P`
/// (`BabyBearField::ONE`'s raw value) — never as a canonical add.
#[inline(always)]
unsafe fn r_mont() -> uint32x4_t {
    vdupq_n_u32(BabyBearField::ONE.raw_u32_value())
}

#[inline(always)]
unsafe fn redc4(acc: &[Acc; 4]) -> [uint32x4_t; 4] {
    [acc[0].redc(), acc[1].redc(), acc[2].redc(), acc[3].redc()]
}

// ---------------------------------------------------------------------------
// operand-grouped term program (built once per layer by the chain)
// ---------------------------------------------------------------------------

/// A grid operand of the layer program: a base slot grid, a bracket-form
/// grid, or an ext slot grid. In the continuing pass every `Slot` / `Form`
/// is an ext grid of the folded tables.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Opnd {
    Slot(u16),
    Form(u16),
    Ext(u16),
}

impl Opnd {
    fn of(r: &FormRef) -> Self {
        match r {
            FormRef::Slot(i) => Opnd::Slot(*i),
            FormRef::Form(i) => Opnd::Form(*i),
        }
    }
}

/// `pivot (x) sum_k coeff_k * member_k`: one shared operand times an
/// ext-coefficient linear combination of the others. A group of ONE member
/// is evaluated directly (`coeff * pivot * member`).
#[derive(Clone, Debug)]
pub(super) struct Group {
    pub(super) pivot: Opnd,
    pub(super) members: Vec<(Opnd, BabyBearExt4)>,
}

/// The layer program's quadratic terms regrouped by shared operand, so that
/// `sum_k c_k a b_k = a * sum_k c_k b_k` costs one product per GROUP instead
/// of one per term — the inner sums are plain coefficient
/// multiply-accumulates. Exact field identities only: the results are
/// bit-identical to the term-by-term evaluation.
#[derive(Clone, Debug, Default)]
pub(super) struct GroupedProgram {
    /// initial pass: base pivot x base members (factored products + QuadBB)
    pub(super) base: Vec<Group>,
    /// initial pass: ext pivot x base members (QuadBE)
    pub(super) base_by_ext: Vec<Group>,
    /// initial pass: ext pivot x ext members (QuadEE)
    pub(super) ext: Vec<Group>,
    /// continuing pass over the folded all-ext tables (products + folded quads)
    pub(super) folded: Vec<Group>,
}

/// Groups `c * a * b` terms by whichever of `a`, `b` occurs in more terms of
/// the list (ties: `a`); group order = first appearance of the pivot.
fn group_by_frequency(terms: &[(Opnd, Opnd, BabyBearExt4)]) -> Vec<Group> {
    use std::collections::BTreeMap;
    let mut freq: BTreeMap<Opnd, usize> = BTreeMap::new();
    for (a, b, _) in terms.iter() {
        *freq.entry(*a).or_default() += 1;
        *freq.entry(*b).or_default() += 1;
    }
    let pivots: Vec<(Opnd, Opnd)> = terms
        .iter()
        .map(|(a, b, _)| {
            if freq[a] >= freq[b] {
                (*a, *b)
            } else {
                (*b, *a)
            }
        })
        .collect();
    group_by_pivot(
        terms
            .iter()
            .zip(pivots.iter())
            .map(|((_, _, c), (p, m))| (*p, *m, *c)),
    )
}

/// Groups `(pivot, member, coeff)` terms by pivot; group order = first
/// appearance of the pivot, members in term order.
fn group_by_pivot(terms: impl Iterator<Item = (Opnd, Opnd, BabyBearExt4)>) -> Vec<Group> {
    let mut groups: Vec<Group> = Vec::new();
    for (pivot, member, c) in terms {
        match groups.iter_mut().find(|g| g.pivot == pivot) {
            Some(g) => g.members.push((member, c)),
            None => groups.push(Group {
                pivot,
                members: vec![(member, c)],
            }),
        }
    }
    groups
}

impl GroupedProgram {
    pub(super) fn new(prog: &OwnedSoaProgram<BabyBearField, BabyBearExt4>) -> Self {
        let products: Vec<(Opnd, Opnd, BabyBearExt4)> = prog
            .products
            .iter()
            .map(|(a, b, c)| (Opnd::of(a), Opnd::of(b), *c))
            .collect();
        let mut base = products.clone();
        let mut base_by_ext = Vec::new();
        let mut ext = Vec::new();
        for step in prog.rest_steps.iter() {
            match step {
                ProgramStep::QuadBB { a, b, c } => base.push((Opnd::Slot(*a), Opnd::Slot(*b), *c)),
                // the ext operand is always the pivot: the members' inner sum
                // is then a base x ext-coefficient MLA (the cheap kind)
                ProgramStep::QuadBE { base: b, ext: e, c } => {
                    base_by_ext.push((Opnd::Ext(*e), Opnd::Slot(*b), *c))
                }
                ProgramStep::QuadEE { a, b, c } => ext.push((Opnd::Ext(*a), Opnd::Ext(*b), *c)),
                _ => {}
            }
        }
        let mut folded = products;
        for (a, b, c) in prog.folded_quad.iter() {
            folded.push((Opnd::Slot(*a), Opnd::Slot(*b), *c));
        }
        GroupedProgram {
            base: group_by_frequency(&base),
            base_by_ext: group_by_pivot(base_by_ext.into_iter()),
            ext: group_by_frequency(&ext),
            folded: group_by_frequency(&folded),
        }
    }

    /// (groups, terms, terms saved) per list, for logging.
    pub(super) fn summary(&self) -> String {
        let one = |g: &[Group]| {
            let terms: usize = g.iter().map(|x| x.members.len()).sum();
            format!("{} groups / {} terms", g.len(), terms)
        };
        format!(
            "base {}; base_by_ext {}; ext {}; folded {}",
            one(&self.base),
            one(&self.base_by_ext),
            one(&self.ext),
            one(&self.folded)
        )
    }
}

/// A group with its operands resolved to this thread's grid addresses and
/// its coefficients broadcast.
struct RGroup {
    pivot: *const u32,
    /// (grid, coefficient limbs, coefficient table)
    members: Vec<(*const u32, uint32x4_t, Coeff)>,
}

unsafe fn resolve(groups: &[Group], f: &dyn Fn(Opnd) -> *const u32) -> Vec<RGroup> {
    groups
        .iter()
        .map(|g| RGroup {
            pivot: f(g.pivot),
            members: g
                .members
                .iter()
                .map(|(m, c)| (f(*m), coeff_vec(c), Coeff::new(c)))
                .collect(),
        })
        .collect()
}

/// Inner sum `sum_k c_k * member_k` over BASE member grids at cell group
/// offset `off` (u32 units), as canonical ext limbs.
#[inline(always)]
unsafe fn inner_base(members: &[(*const u32, uint32x4_t, Coeff)], off: usize) -> [uint32x4_t; 4] {
    let mut inner = [Acc::zero(); 4];
    let mut t = 0u32;
    for (m, cv, _) in members.iter() {
        mla4(&mut inner, vld1q_u32(m.add(off)), *cv);
        t += 1;
        if t == 2 {
            condsub4(&mut inner);
            t = 0;
        }
    }
    redc4(&inner)
}

/// Inner sum `sum_k c_k (x) member_k` over EXT member grids at cell group
/// offset `off` (u32 units), as canonical ext limbs.
#[inline(always)]
unsafe fn inner_ext(members: &[(*const u32, uint32x4_t, Coeff)], off: usize) -> [uint32x4_t; 4] {
    let mut inner = [Acc::zero(); 4];
    for (m, _, k) in members.iter() {
        table_mla4(&mut inner, &load_cell(m.add(off)), k);
    }
    redc4(&inner)
}

/// INITIAL pass: one register-resident sweep of every term over groups
/// `g0 .. g0 + N` of the current row; writes the canonical cell values of
/// those groups into `lazy_out` (layout `16 * group + 4 * limb`).
///
/// Range bookkeeping: `ticks` counts raw `< P^2` products added to the
/// accumulators since their last condsub; a condsub runs at 2. Table multiplies need `acc < R P` on
/// entry (`settle!`) and leave it so.
#[inline(always)]
unsafe fn sweep_initial<const N: usize>(
    g0: usize,
    base: &[RGroup],
    base_by_ext: &[RGroup],
    ext: &[RGroup],
    lin_b: &[(*const u32, uint32x4_t)],
    lin_e: &[(*const u32, Coeff)],
    r11v: uint32x4_t,
    lazy_out: *mut u32,
) {
    let mut acc = [[Acc::zero(); 4]; N];
    let rm = r_mont();
    let mut ticks = 0u32;
    macro_rules! tick {
        () => {
            ticks += 1;
            if ticks == 2 {
                for g in 0..N {
                    condsub4(&mut acc[g]);
                }
                ticks = 0;
            }
        };
    }
    macro_rules! settle {
        () => {
            if ticks != 0 {
                for g in 0..N {
                    condsub4(&mut acc[g]);
                }
                ticks = 0;
            }
        };
    }

    // ext pivot x ext members
    for grp in ext.iter() {
        if let [(m, _, k)] = grp.members.as_slice() {
            settle!();
            for g in 0..N {
                let off = 16 * (g0 + g);
                let w = ext_mul_lazy(&load_cell(grp.pivot.add(off)), &load_cell(m.add(off)), r11v);
                table_mla4(&mut acc[g], &w, k);
            }
        } else {
            for g in 0..N {
                let off = 16 * (g0 + g);
                let inner = inner_ext(&grp.members, off);
                let w = ext_mul_lazy(&load_cell(grp.pivot.add(off)), &inner, r11v);
                for l in 0..4 {
                    acc[g][l].mla(w[l], rm);
                }
            }
            tick!();
        }
    }
    // ext pivot x base members
    for grp in base_by_ext.iter() {
        if let [(m, _, k)] = grp.members.as_slice() {
            settle!();
            for g in 0..N {
                let bv = vld1q_u32(m.add(4 * (g0 + g)));
                let pe = grp.pivot.add(16 * (g0 + g));
                let t: [uint32x4_t; 4] =
                    core::array::from_fn(|l| neon::mont_mul4(vld1q_u32(pe.add(4 * l)), bv));
                table_mla4(&mut acc[g], &t, k);
            }
        } else {
            for g in 0..N {
                let inner = inner_base(&grp.members, 4 * (g0 + g));
                let w = ext_mul_lazy(&load_cell(grp.pivot.add(16 * (g0 + g))), &inner, r11v);
                for l in 0..4 {
                    acc[g][l].mla(w[l], rm);
                }
            }
            tick!();
        }
    }
    // ext linear terms: binary cells only
    if g0 < NBIN {
        for (m, k) in lin_e.iter() {
            settle!();
            for g in 0..N {
                if g0 + g < NBIN {
                    table_mla4(&mut acc[g], &load_cell(m.add(16 * (g0 + g))), k);
                }
            }
        }
    }
    // base pivot x base members
    for grp in base.iter() {
        if let [(m, cv, _)] = grp.members.as_slice() {
            for g in 0..N {
                let off = 4 * (g0 + g);
                let t = neon::mont_mul4(vld1q_u32(grp.pivot.add(off)), vld1q_u32(m.add(off)));
                mla4(&mut acc[g], t, *cv);
            }
            tick!();
        } else {
            for g in 0..N {
                let off = 4 * (g0 + g);
                let inner = inner_base(&grp.members, off);
                let pv = vld1q_u32(grp.pivot.add(off));
                // raw (R^2-scaled) products straight into the accumulator
                for l in 0..4 {
                    acc[g][l].mla(pv, inner[l]);
                }
            }
            tick!();
        }
    }
    // base linear terms: binary cells only
    if g0 < NBIN {
        for (m, cv) in lin_b.iter() {
            for g in 0..N {
                if g0 + g < NBIN {
                    mla4(&mut acc[g], vld1q_u32(m.add(4 * (g0 + g))), *cv);
                }
            }
            tick!();
        }
    }
    for g in 0..N {
        for l in 0..4 {
            vst1q_u32(lazy_out.add(16 * (g0 + g) + 4 * l), acc[g][l].redc());
        }
    }
}

/// CONTINUING pass: the same sweep over the all-ext folded tables.
#[inline(always)]
unsafe fn sweep_continuing<const N: usize>(
    g0: usize,
    folded: &[RGroup],
    lin: &[(*const u32, Coeff)],
    r11v: uint32x4_t,
    lazy_out: *mut u32,
) {
    let mut acc = [[Acc::zero(); 4]; N];
    let rm = r_mont();
    let mut ticks = 0u32;
    macro_rules! settle {
        () => {
            if ticks != 0 {
                for g in 0..N {
                    condsub4(&mut acc[g]);
                }
                ticks = 0;
            }
        };
    }
    for grp in folded.iter() {
        if let [(m, _, k)] = grp.members.as_slice() {
            settle!();
            for g in 0..N {
                let off = 16 * (g0 + g);
                let w = ext_mul_lazy(&load_cell(grp.pivot.add(off)), &load_cell(m.add(off)), r11v);
                table_mla4(&mut acc[g], &w, k);
            }
        } else {
            for g in 0..N {
                let off = 16 * (g0 + g);
                let inner = inner_ext(&grp.members, off);
                let w = ext_mul_lazy(&load_cell(grp.pivot.add(off)), &inner, r11v);
                for l in 0..4 {
                    acc[g][l].mla(w[l], rm);
                }
            }
            ticks += 1;
            if ticks == 2 {
                for g in 0..N {
                    condsub4(&mut acc[g]);
                }
                ticks = 0;
            }
        }
    }
    if g0 < NBIN {
        for (m, k) in lin.iter() {
            settle!();
            for g in 0..N {
                if g0 + g < NBIN {
                    table_mla4(&mut acc[g], &load_cell(m.add(16 * (g0 + g))), k);
                }
            }
        }
    }
    for g in 0..N {
        for l in 0..4 {
            vst1q_u32(lazy_out.add(16 * (g0 + g) + 4 * l), acc[g][l].redc());
        }
    }
}

/// Sum of per-chunk accumulators (exact field addition, order-independent).
fn reduce_chunks(chunks: &[[BabyBearExt4; 27]]) -> [BabyBearExt4; 27] {
    let mut out = [BabyBearExt4::ZERO; 27];
    for chunk in chunks.iter() {
        for i in 0..27 {
            out[i].add_assign(&chunk[i]);
        }
    }
    out
}

/// The window-3 INITIAL pass: T-weighted `{0,1,inf}^3` accumulator (NEON SoA
/// cell order) of the layer program over the ORIGINAL inputs, `rows` rows of
/// 8 trace points each, `t_suffix[row]` the scalar suffix-eq weight.
pub(super) fn window_initial_pass_regacc(
    prog: &OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    grouped: &GroupedProgram,
    base_polys: &[&[BabyBearField]],
    ext_polys: &[&[BabyBearExt4]],
    t_suffix: &[BabyBearExt4],
    rows: usize,
    worker: &Worker,
) -> [BabyBearExt4; 27] {
    assert_eq!(t_suffix.len(), rows);
    assert_eq!(base_polys.len(), prog.base_interp.len());
    assert_eq!(ext_polys.len(), prog.ext_interp.len());
    for p in base_polys.iter() {
        assert!(p.len() >= rows * 8);
    }
    for p in ext_polys.iter() {
        assert!(p.len() >= rows * 8);
    }
    let base_ptrs: Vec<usize> = base_polys.iter().map(|p| p.as_ptr() as usize).collect();
    let ext_ptrs: Vec<usize> = ext_polys.iter().map(|p| p.as_ptr() as usize).collect();

    let geometry = worker.get_geometry_with_threshold(rows, PAR_THRESHOLD);
    let mut acc_chunks = vec![[BabyBearExt4::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let base_ptrs = base_ptrs.clone();
            let ext_ptrs = ext_ptrs.clone();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let r11v = neon::soa_r11v();
                let const_bcast = neon::soa_broadcast_ext(&prog.additive_constant);
                let has_const = !prog.additive_constant.is_zero();
                // per-row scratch: grids (base, ext, forms), the sweeps'
                // canonical output, the constant's canonical cells, the
                // running SoA accumulator
                let mut base_flat = vec![0u32; base_ptrs.len() * BS];
                let mut ext_flat = vec![0u32; ext_ptrs.len() * ES];
                let mut form_flat = vec![0u32; prog.forms.len() * BS];
                let mut lazy_out = vec![0u32; ES];
                let mut const_cells = vec![0u32; ES];
                let mut acc_soa = vec![0u32; ES];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 4 * NG];
                let bptr = base_flat.as_mut_ptr();
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lo = lazy_out.as_mut_ptr();
                let cptr = const_cells.as_mut_ptr();
                // the grouped terms with this thread's grid addresses
                let at = |o: Opnd| -> *const u32 {
                    match o {
                        Opnd::Slot(i) => bptr.add(i as usize * BS) as *const u32,
                        Opnd::Form(i) => fptr.add(i as usize * BS) as *const u32,
                        Opnd::Ext(i) => xptr.add(i as usize * ES) as *const u32,
                    }
                };
                let g_base = resolve(&grouped.base, &at);
                let g_be = resolve(&grouped.base_by_ext, &at);
                let g_ext = resolve(&grouped.ext, &at);
                let lin_b: Vec<(*const u32, uint32x4_t)> = prog
                    .rest_steps
                    .iter()
                    .filter_map(|s| match s {
                        ProgramStep::LinB { i, c } => Some((at(Opnd::Slot(*i)), coeff_vec(c))),
                        _ => None,
                    })
                    .collect();
                let lin_e: Vec<(*const u32, Coeff)> = prog
                    .rest_steps
                    .iter()
                    .filter_map(|s| match s {
                        ProgramStep::LinE { i, c } => Some((at(Opnd::Ext(*i)), Coeff::new(c))),
                        _ => None,
                    })
                    .collect();

                for row in chunk_start..chunk_start + chunk_size {
                    // grids
                    for (i, &src) in base_ptrs.iter().enumerate() {
                        fill_base_w3_vec(
                            bptr.add(i * BS),
                            src as *const u32,
                            row,
                            prog.base_interp[i],
                        );
                    }
                    for (i, &src) in ext_ptrs.iter().enumerate() {
                        fill_ext_w3_vec(
                            xptr.add(i * ES),
                            src as *const BabyBearExt4,
                            row,
                            prog.ext_interp[i],
                            ext_tmp.as_mut_ptr(),
                        );
                    }
                    // forms
                    for (f, form) in prog.forms.iter().enumerate() {
                        let g = fptr.add(f * BS);
                        let mut members = form.members.iter();
                        match members.next() {
                            Some((op, idx)) => apply_form_op_first::<BabyBearField, NG>(
                                g,
                                bptr.add(*idx as usize * BS),
                                op,
                            ),
                            None => core::ptr::write_bytes(g, 0, BS),
                        }
                        for (op, idx) in members {
                            apply_form_op::<BabyBearField, NG>(g, bptr.add(*idx as usize * BS), op);
                        }
                        if !form.constant.is_zero() {
                            neon::soa_base_form_add_const_n::<NBIN>(g, form.constant);
                        }
                    }
                    // every term, register-resident per group range
                    sweep_initial::<2>(0, &g_base, &g_be, &g_ext, &lin_b, &lin_e, r11v, lo);
                    sweep_initial::<2>(2, &g_base, &g_be, &g_ext, &lin_b, &lin_e, r11v, lo);
                    sweep_initial::<2>(4, &g_base, &g_be, &g_ext, &lin_b, &lin_e, r11v, lo);
                    sweep_initial::<1>(6, &g_base, &g_be, &g_ext, &lin_b, &lin_e, r11v, lo);
                    // the additive constant lives in the canonical domain on
                    // the binary cells (`const_cells` is re-zeroed by the eq
                    // step)
                    if has_const {
                        neon::soa_add_const_all_n::<NBIN>(cptr, &const_bcast);
                    }
                    // eq weight of the row, accumulate
                    let eqb = neon::soa_broadcast_ext(&t_suffix[row]);
                    neon::soa_apply_eq_and_accumulate::<NG>(
                        acc_soa.as_mut_ptr(),
                        lazy_out.as_ptr(),
                        cptr,
                        &eqb,
                        r11v,
                    );
                }

                *acc_dst = finish_soa_acc::<BabyBearExt4, NG, 27>(&acc_soa, &mut ext_tmp);
            })
        }
    });

    reduce_chunks(&acc_chunks)
}

/// The window-3 CONTINUING pass over the folded all-ext tables (`folded` in
/// `base ++ ext` slot order, each `>= 8 * rows` entries), `interp[slot]` =
/// the slot is read at the infinity cells.
pub(super) fn window_continuing_pass_regacc(
    prog: &OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    grouped: &GroupedProgram,
    interp: &[bool],
    folded: &[&[BabyBearExt4]],
    t_suffix: &[BabyBearExt4],
    rows: usize,
    worker: &Worker,
) -> [BabyBearExt4; 27] {
    assert_eq!(t_suffix.len(), rows);
    assert_eq!(interp.len(), folded.len());
    for p in folded.iter() {
        assert!(p.len() >= rows * 8);
    }
    let ptrs: Vec<usize> = folded.iter().map(|p| p.as_ptr() as usize).collect();

    let geometry = worker.get_geometry_with_threshold(rows, PAR_THRESHOLD);
    let mut acc_chunks = vec![[BabyBearExt4::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let ptrs = ptrs.clone();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let r11v = neon::soa_r11v();
                let const_bcast = neon::soa_broadcast_ext(&prog.additive_constant);
                let has_const = !prog.additive_constant.is_zero();
                let mut ext_flat = vec![0u32; ptrs.len() * ES];
                let mut form_flat = vec![0u32; prog.forms.len() * ES];
                let mut lazy_out = vec![0u32; ES];
                let mut acc_soa = vec![0u32; ES];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 4 * NG];
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lo = lazy_out.as_mut_ptr();
                let at = |o: Opnd| -> *const u32 {
                    match o {
                        Opnd::Slot(i) | Opnd::Ext(i) => xptr.add(i as usize * ES) as *const u32,
                        Opnd::Form(i) => fptr.add(i as usize * ES) as *const u32,
                    }
                };
                let g_folded = resolve(&grouped.folded, &at);
                let lin: Vec<(*const u32, Coeff)> = prog
                    .folded_lin
                    .iter()
                    .map(|(i, c)| (at(Opnd::Slot(*i)), Coeff::new(c)))
                    .collect();

                for row in chunk_start..chunk_start + chunk_size {
                    for (i, &src) in ptrs.iter().enumerate() {
                        fill_ext_w3_vec(
                            xptr.add(i * ES),
                            src as *const BabyBearExt4,
                            row,
                            interp[i],
                            ext_tmp.as_mut_ptr(),
                        );
                    }
                    for (f, form) in prog.forms.iter().enumerate() {
                        let g = fptr.add(f * ES);
                        let mut members = form.members.iter();
                        match members.next() {
                            Some((op, idx)) => apply_ext_form_op_first::<BabyBearField, NG>(
                                g,
                                xptr.add(*idx as usize * ES),
                                op,
                            ),
                            None => core::ptr::write_bytes(g, 0, ES),
                        }
                        for (op, idx) in members {
                            apply_ext_form_op::<BabyBearField, NG>(
                                g,
                                xptr.add(*idx as usize * ES),
                                op,
                            );
                        }
                        if !form.constant.is_zero() {
                            neon::soa_ext_form_add_base_const_n::<NBIN>(g, form.constant);
                        }
                    }
                    sweep_continuing::<2>(0, &g_folded, &lin, r11v, lo);
                    sweep_continuing::<2>(2, &g_folded, &lin, r11v, lo);
                    sweep_continuing::<2>(4, &g_folded, &lin, r11v, lo);
                    sweep_continuing::<1>(6, &g_folded, &lin, r11v, lo);
                    if has_const {
                        // canonical domain, binary cells, after the REDC
                        neon::soa_add_const_all_n::<NBIN>(lo, &const_bcast);
                    }
                    let eqb = neon::soa_broadcast_ext(&t_suffix[row]);
                    neon::soa_apply_eq_and_accumulate_n::<NG>(acc_soa.as_mut_ptr(), lo, &eqb, r11v);
                }

                *acc_dst = finish_soa_acc::<BabyBearExt4, NG, 27>(&acc_soa, &mut ext_tmp);
            })
        }
    });

    reduce_chunks(&acc_chunks)
}

// ---------------------------------------------------------------------------
// window-3 grid fills with VECTOR extrapolation (lever 3)
// ---------------------------------------------------------------------------

/// Canonical `a - b mod P` lane-wise for canonical inputs.
#[inline(always)]
unsafe fn sub_mod4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let d = vsubq_u32(a, b);
    let under = vcgtq_u32(b, a);
    vaddq_u32(d, vandq_u32(under, vdupq_n_u32(P)))
}

/// Byte-index vector selecting the 32-bit elements `e[0..4]` of a
/// `vqtbl3q_u8` table of three 32-bit x 4 registers (element `e` = table
/// bytes `4e .. 4e+4`; `0xFF` lanes read as zero).
const fn tbl_idx(e: [u8; 4]) -> [u8; 16] {
    let mut out = [0xFFu8; 16];
    let mut i = 0;
    while i < 4 {
        if e[i] != 0xFF {
            let mut k = 0;
            while k < 4 {
                out[4 * i + k] = 4 * e[i] + k as u8;
                k += 1;
            }
        }
        i += 1;
    }
    out
}

// Table = {cells 0..4, cells 4..8, cells 8..12}; element index = cell index.
const IDX_C12_A: [u8; 16] = tbl_idx([2, 3, 9, 6]);
const IDX_C12_B: [u8; 16] = tbl_idx([0, 1, 8, 4]);
const IDX_C16_A: [u8; 16] = tbl_idx([7, 11, 0xFF, 0xFF]);
const IDX_C16_B: [u8; 16] = tbl_idx([5, 10, 0xFF, 0xFF]);
const IDX_C18_A: [u8; 16] = tbl_idx([4, 5, 10, 6]);
const IDX_C18_B: [u8; 16] = tbl_idx([0, 1, 8, 2]);
const IDX_C22_A: [u8; 16] = tbl_idx([7, 11, 0xFF, 0xFF]);
const IDX_C22_B: [u8; 16] = tbl_idx([3, 9, 0xFF, 0xFF]);

/// Window-3 base grid fill: the 8 taps of `row` into cells 0..8 and, when
/// the slot is read at the infinity cells, the 19 `W3_INF` extrapolations
/// (cell `d` = cell `hi` - cell `lo`, see `lsb_bench::W3_INF`) computed as
/// gathered vector differences:
/// * cells  8..12 = odd taps - even taps,
/// * cells 12..18 = (2-0, 3-1, 9-8, 6-4, 7-5, 11-10),
/// * cells 18..27 = (4-0, 5-1, 10-8, 6-2, 7-3, 11-9, 15-12, 16-13, 17-14).
/// Cell 27 (the pad) stays zero.
#[inline(always)]
unsafe fn fill_base_w3_vec(dst: *mut u32, src: *const u32, row: usize, interpolate: bool) {
    let p = src.add(row * 8);
    let t0 = vld1q_u32(p);
    let t1 = vld1q_u32(p.add(4));
    vst1q_u32(dst, t0);
    vst1q_u32(dst.add(4), t1);
    if !interpolate {
        return;
    }
    // cells 8..12
    let c8 = sub_mod4(vuzp2q_u32(t0, t1), vuzp1q_u32(t0, t1));
    vst1q_u32(dst.add(8), c8);
    let tbl = uint8x16x3_t(
        vreinterpretq_u8_u32(t0),
        vreinterpretq_u8_u32(t1),
        vreinterpretq_u8_u32(c8),
    );
    let gather = |idx: &[u8; 16]| -> uint32x4_t {
        vreinterpretq_u32_u8(vqtbl3q_u8(tbl, vld1q_u8(idx.as_ptr())))
    };
    // cells 12..16 and 16..18
    let c12 = sub_mod4(gather(&IDX_C12_A), gather(&IDX_C12_B));
    vst1q_u32(dst.add(12), c12);
    let c16 = sub_mod4(gather(&IDX_C16_A), gather(&IDX_C16_B));
    vst1_u32(dst.add(16), vget_low_u32(c16));
    // cells 18..22 and 22..24
    let c18 = sub_mod4(gather(&IDX_C18_A), gather(&IDX_C18_B));
    vst1q_u32(dst.add(18), c18);
    let c22 = sub_mod4(gather(&IDX_C22_A), gather(&IDX_C22_B));
    vst1_u32(dst.add(22), vget_low_u32(c22));
    // cells 24..27 = (15-12, 16-13, 17-14); lane 3 would be the pad: keep it 0
    let hi = vextq_u32::<3>(c12, c16);
    let c24 = vsetq_lane_u32::<3>(0, sub_mod4(hi, c12));
    vst1q_u32(dst.add(24), c24);
}

/// Window-3 ext grid fill: AoS copy of the 8 taps, the 19 extrapolations as
/// whole-`Ext4` vector differences (one `Ext4` = one `uint32x4_t`, limbs are
/// independent), then the limb-major transpose into the 7-group SoA grid
/// (same layout as `lsb_bench::fill_ext_w3_soa`).
#[inline(always)]
unsafe fn fill_ext_w3_vec(
    grid: *mut u32,
    src: *const BabyBearExt4,
    row: usize,
    interpolate: bool,
    tmp: *mut BabyBearExt4,
) {
    let s = src.add(row * 8) as *const u32;
    let t = tmp as *mut u32;
    for i in 0..8 {
        vst1q_u32(t.add(4 * i), vld1q_u32(s.add(4 * i)));
    }
    if interpolate {
        for (d, hi, lo) in W3_INF {
            let v = sub_mod4(
                vld1q_u32(t.add(4 * hi as usize)),
                vld1q_u32(t.add(4 * lo as usize)),
            );
            vst1q_u32(t.add(4 * d as usize), v);
        }
    }
    for g in 0..7 {
        let v = neon::soa_transpose_ext4(tmp.add(4 * g));
        neon::soa_store_cell(grid.add(16 * g), &v);
    }
}
