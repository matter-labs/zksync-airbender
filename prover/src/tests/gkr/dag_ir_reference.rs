//! Shared value oracle for the DAG-IR differential tests (Tasks 6 + 13).
//!
//! This module is the **prover-side authoritative ground truth** for the new
//! GKR DAG-IR evaluator. Per spec §8 it is derived **independently of
//! `lower_dag`**: the per-relation value formulas here mirror the prover's own
//! forward-loop / sumcheck-kernel math, NOT the DAG generator's lowering. The
//! retired codegen path is explicitly NOT used as an oracle (it bakes challenges
//! into opaque leaves and cannot reproduce folded values).
//!
//! Both consumers — the Task-6 `dag_ir_oracle` spike and the Task-13
//! `dag_ir_differential` harness — share ONE copy of:
//!   * [`RefCtx`]              — the single source of binding truth (storage,
//!                               challenges, lookup mapping, virtual setups),
//!   * [`reference_relation_values`] — the exhaustive per-relation value oracle,
//!   * the real [`StorageReadResolver`] / [`RefLookupResolver`] /
//!     [`RefVirtualSetupResolver`] / [`RefChallengeResolver`] fed to the DAG-IR
//!     evaluator.
//!
//! Binding scheme: one shared assignment for every quantity the relations read
//! (one base value per [`GKRAddress`], one base value per lookup
//! `(kind, set_index, query, row)`, one base value per `(VirtualSetupKind, row)`,
//! and a fixed set of extension challenges). The reference math reads those; the
//! DAG-IR resolvers read the SAME values. Equal inputs ⇒ the two evaluators must
//! agree slot-for-slot. The independence is in the ARITHMETIC: the reference
//! computes each relation's value from the prover formula, the DAG IR from its
//! own lowered `Expr`; only the leaf bindings are shared.
//!
//! Field-conversion convention: the reference + resolvers use
//! `from_u32_with_reduction` throughout. The prover kernels use
//! `from_u32_unchecked`; these coincide for in-range coefficients, and all
//! sampled-fixture coefficients are kept well under `2^16`, so the comparison is
//! exact, not spuriously divergent (controller ambiguity-resolution #3).

use std::collections::BTreeSet;

use cs::definitions::{
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::definitions::gkr::{
    AddressSpaceType, NoFieldLinearRelation, NoFieldSingleColumnLookupRelation,
    NoFieldVectorLookupRelation, RamWordRepresentation,
};
use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::dag_ir::{
    Bf, ChallengeKey, ChallengeRef, ChallengeResolver, Ext, LookupResolver, LookupValueKind,
    PermutationSlot, ReadPlace, ReadResolver, VirtualSetupKind, VirtualSetupResolver,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation, NoFieldMaxQuadraticConstraintsGKRRelation,
    NoFieldMaxQuadraticGKRRelation, NoFieldSpecialMemoryContributionRelation,
};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};

use crate::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRStorage};

pub(crate) type F = BabyBearField;
pub(crate) type E = BabyBearExt4;

// ── lift helper (mirrors dag_ir::eval::lift) ───────────────────────────────

#[inline(always)]
pub(crate) fn lift(b: F) -> E {
    <E as FieldExtension<F>>::from_base(b)
}

// ── deterministic pseudo-random base assignment ────────────────────────────

/// Fixed deterministic pseudo-random base value for a `GKRAddress`. Same seed on
/// both the reference and the IR side, so the binding is identical. Values are
/// masked well under `2^16` so any range-check / wrapping semantics stay valid
/// and the `from_u32_with_reduction` vs `from_u32_unchecked` conventions agree.
pub(crate) fn assign_base_value(addr: GKRAddress) -> F {
    let key: u64 = match addr {
        GKRAddress::BaseLayerWitness(o) => 0x1000_0000_0000_0000 ^ (o as u64),
        GKRAddress::BaseLayerMemory(o) => 0x2000_0000_0000_0000 ^ (o as u64),
        GKRAddress::Setup(o) => 0x3000_0000_0000_0000 ^ (o as u64),
        GKRAddress::InnerLayer { layer, offset } => {
            0x4000_0000_0000_0000 ^ ((layer as u64) << 32) ^ (offset as u64)
        }
        GKRAddress::Cached { layer, offset } => {
            0x5000_0000_0000_0000 ^ ((layer as u64) << 32) ^ (offset as u64)
        }
        GKRAddress::VirtualSetup(poly) => 0x6000_0000_0000_0000 ^ (poly as u64),
        other => panic!("address {:?} not expected as a base input", other),
    };
    scramble(key)
}

/// splitmix64-style scramble of a stable key into a small in-range field value.
fn scramble(key: u64) -> F {
    let mut z = key.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;
    // keep it well under 2^16 (range-check / U16 safe), then reduce.
    F::from_u32_with_reduction((z as u32) & 0x0000_FFFF)
}

// ── shared binding context ─────────────────────────────────────────────────

/// The single source of binding truth. Holds:
///   * `storage`            — one fixed base value per `GKRAddress` (base layer);
///   * the four extension challenges used across relation families;
///   * the inits/teardowns `high_bits_offset` actually in effect.
pub(crate) struct RefCtx {
    pub storage: GKRStorage<F, E>,
    /// `gamma`: lookup additive challenge.
    pub lookup_additive: E,
    /// `alpha`: lookup multiplicative challenge base (powers are `alpha^j`).
    pub lookup_multiplicative: E,
    /// permutation argument additive challenge.
    pub permutation_additive: E,
    /// the six permutation linearization challenges, indexed by the prover's
    /// flat `*_IDX` layout (AddressLow=0 .. ValueHigh=5).
    pub permutation_linearization: [E; 6],
    /// `rho`: constraint aggregation challenge base (powers `rho^p`).
    pub constraint_aggregation: E,
    /// inits/teardowns high-bits shift in effect (0 when the artifact carries no
    /// `inits_and_teardowns_word_bits`, matching the IR lowering).
    pub inits_high_bits_offset: u32,
}

impl RefCtx {
    /// Build a context binding a fixed random base value for every address in
    /// `addrs`, plus a fixed nontrivial set of challenges.
    pub(crate) fn new(addrs: &BTreeSet<GKRAddress>, trace_len: usize) -> Self {
        assert!(trace_len.is_power_of_two());
        let mut storage = GKRStorage::<F, E>::default();
        storage.layers.push(Default::default());
        for &addr in addrs {
            let v = assign_base_value(addr);
            let values: Box<[F]> = vec![v; trace_len].into_boxed_slice();
            storage.insert_base_field_at_layer(0, addr, BaseFieldPoly::new(values));
        }

        let challenge = |a, b, c, d| {
            E::from_array_of_base([
                F::from_u32_with_reduction(a),
                F::from_u32_with_reduction(b),
                F::from_u32_with_reduction(c),
                F::from_u32_with_reduction(d),
            ])
        };

        Self {
            storage,
            lookup_additive: challenge(7, 13, 1009, 40_000),
            lookup_multiplicative: challenge(3, 101, 555, 12_345),
            permutation_additive: challenge(11, 22, 33, 44),
            permutation_linearization: [
                challenge(2, 3, 5, 7),
                challenge(11, 13, 17, 19),
                challenge(23, 29, 31, 37),
                challenge(41, 43, 47, 53),
                challenge(59, 61, 67, 71),
                challenge(73, 79, 83, 89),
            ],
            constraint_aggregation: challenge(97, 101, 103, 107),
            // synthetic single-relation artifacts carry no word_bits → offset 0,
            // matching `dag_ir::lower::memory::top_bits_const`.
            inits_high_bits_offset: 0,
        }
    }

    /// Override the inits/teardowns `high_bits_offset` to match the IR lowering
    /// for a given artifact. The IR computes
    /// `high_bits_offset = (log2(trace_len) + word_bits).saturating_sub(16)`
    /// when `word_bits` is present, else `0` (see
    /// `dag_ir::lower::memory::top_bits_const`). The golden harness must mirror
    /// the SAME offset so the `set_idx << offset` top-bits term agrees.
    pub(crate) fn with_inits_offset(mut self, trace_len: usize, word_bits: Option<u32>) -> Self {
        self.inits_high_bits_offset = match word_bits {
            Some(wb) if trace_len.is_power_of_two() && trace_len > 0 => {
                (trace_len.trailing_zeros() + wb).saturating_sub(16)
            }
            _ => 0,
        };
        self
    }

    pub(crate) fn read_base(&self, addr: GKRAddress, row: usize) -> F {
        // The IR's `map_address` routes a `VirtualSetup` address to a
        // `SourceKind::VirtualSetup` (resolved by the virtual-setup resolver),
        // NOT a storage read. Mirror that: any `VirtualSetup` leaf — including
        // one appearing inside a lookup-query linear combination — resolves via
        // the SAME virtual-setup mapping the IR resolver uses, so the two sides
        // agree.
        if let GKRAddress::VirtualSetup(poly) = addr {
            return self.virtual_setup_value(&map_virtual_setup(poly), row);
        }
        self.storage
            .try_get_base_poly(addr)
            .unwrap_or_else(|| panic!("no base poly bound for {:?}", addr))[row]
    }

    /// `alpha^j`.
    fn alpha_pow(&self, j: u32) -> E {
        let mut acc = E::ONE;
        for _ in 0..j {
            acc.mul_assign(&self.lookup_multiplicative);
        }
        acc
    }

    /// `rho^p`.
    fn rho_pow(&self, p: usize) -> E {
        let mut acc = E::ONE;
        for _ in 0..p {
            acc.mul_assign(&self.constraint_aggregation);
        }
        acc
    }

    fn perm_lin(&self, idx: usize) -> E {
        self.permutation_linearization[idx]
    }

    fn perm_lin_slot(&self, slot: &PermutationSlot) -> E {
        self.permutation_linearization[perm_slot_idx(slot)]
    }

    // ── leaf resolution mirroring the IR resolvers ──

    /// Resolve a lookup value the SAME way the IR resolver does — a deterministic
    /// function of `(kind, set_index, query_value, row)`. The reference reads
    /// THIS for any lookup leaf, the IR `LookupResolver` reads the SAME. Returns
    /// a base value.
    fn lookup_value(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        query_value: E,
        row: usize,
    ) -> F {
        // A pure function of its inputs. We do NOT consult a real witness lookup
        // mapping (the synthetic single-relation artifacts have none); instead we
        // bind a deterministic value keyed by the lookup identity. Both sides use
        // this identical resolver, so the comparison tests only the surrounding
        // num/den arithmetic. `query_value` is hashed via its first base coeff
        // (the materialized query is a base linear combination).
        let kind_tag: u64 = match kind {
            LookupValueKind::RangeCheck16Index => 1,
            LookupValueKind::TimestampIndex => 2,
            LookupValueKind::GenericColumn { column } => 0x100 + *column as u64,
            LookupValueKind::DecoderColumn { column } => 0x200 + *column as u64,
        };
        let q =
            <E as FieldExtension<F>>::into_coeffs(query_value)[0].as_u32_reduced() as u64;
        scramble(
            0x7000_0000_0000_0000
                ^ kind_tag.rotate_left(48)
                ^ (set_index as u64).rotate_left(32)
                ^ (row as u64).rotate_left(16)
                ^ q,
        )
    }

    /// Resolve a virtual-setup base value (deterministic, by kind + row).
    fn virtual_setup_value(&self, kind: &VirtualSetupKind, row: usize) -> F {
        let tag: u64 = match kind {
            VirtualSetupKind::RangeCheck16Bits => 1,
            VirtualSetupKind::RangeCheckTimestamp => 2,
            VirtualSetupKind::InitsAndTeardownsLow => 3,
            VirtualSetupKind::InitsAndTeardownsHigh => 4,
        };
        scramble(0x8000_0000_0000_0000 ^ tag.rotate_left(32) ^ (row as u64))
    }

    fn challenge(&self, r: &ChallengeRef) -> E {
        match &r.key {
            ChallengeKey::LookupAdditive => self.lookup_additive,
            ChallengeKey::LookupMultiplicative => match r.power {
                cs::gkr_compiler::dag_ir::ChallengePower::One => self.lookup_multiplicative,
                cs::gkr_compiler::dag_ir::ChallengePower::Static(j) => self.alpha_pow(j),
            },
            ChallengeKey::PermutationAdditive => self.permutation_additive,
            ChallengeKey::PermutationLinearization(slot) => self.perm_lin_slot(slot),
            ChallengeKey::ConstraintAggregation => match r.power {
                cs::gkr_compiler::dag_ir::ChallengePower::One => self.constraint_aggregation,
                cs::gkr_compiler::dag_ir::ChallengePower::Static(p) => self.rho_pow(p as usize),
            },
        }
    }

    /// Build a `GKRExternalChallenges` view of this context (for the explicit
    /// memory-tuple ground-truth check via the real `evaluate_memory_query`).
    pub(crate) fn external_challenges(
        &self,
    ) -> crate::definitions::GKRExternalChallenges<F, E> {
        crate::definitions::GKRExternalChallenges {
            permutation_argument_linearization_challenges: std::array::from_fn(|i| {
                self.permutation_linearization[i]
            }),
            permutation_argument_additive_part: self.permutation_additive,
            _marker: core::marker::PhantomData,
        }
    }

    /// Build the `base_layer_memory_sources` slice view for the real prover
    /// `evaluate_memory_query` (column-indexed `BaseLayerMemory`). Columns the
    /// caller did not bind get a fixed placeholder poly (`zero_pad`); the prover
    /// only indexes the columns the descriptor actually reads, so placeholders
    /// for gaps are never observed.
    pub(crate) fn base_layer_memory_sources<'a>(
        &'a self,
        max_column: usize,
        zero_pad: &'a [F],
    ) -> Vec<&'a [F]> {
        (0..=max_column)
            .map(|c| {
                self.storage
                    .try_get_base_poly(GKRAddress::BaseLayerMemory(c))
                    .unwrap_or(zero_pad)
            })
            .collect()
    }
}

/// Map a `VirtualSetupPoly` to the DAG-IR `VirtualSetupKind` (mirrors
/// `dag_ir::lower::map_virtual_setup`).
fn map_virtual_setup(poly: VirtualSetupPoly) -> VirtualSetupKind {
    match poly {
        VirtualSetupPoly::RangeCheck16Bits => VirtualSetupKind::RangeCheck16Bits,
        VirtualSetupPoly::RangeCheckTimestamp => VirtualSetupKind::RangeCheckTimestamp,
        VirtualSetupPoly::InitsAndTeardownsLow => VirtualSetupKind::InitsAndTeardownsLow,
        VirtualSetupPoly::InitsAndTeardownsHigh => VirtualSetupKind::InitsAndTeardownsHigh,
    }
}

/// Map a `PermutationSlot` onto the prover's flat challenge-power index.
fn perm_slot_idx(slot: &PermutationSlot) -> usize {
    match slot {
        PermutationSlot::AddressLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
        PermutationSlot::AddressHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
        PermutationSlot::TimestampLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
        PermutationSlot::TimestampHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
        PermutationSlot::ValueLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
        PermutationSlot::ValueHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    }
}

// ── query / operand evaluation (mirrors the prover's own leaf math) ─────────

/// `constant + Σ c_i·x_i` in the base field. Mirrors
/// `evaluate_linear_relation_at_row` (forward_loop/utils.rs:206).
fn eval_linear(lin: &NoFieldLinearRelation, ctx: &RefCtx, row: usize) -> F {
    let mut result = F::from_u32_with_reduction(lin.constant);
    for (c, addr) in lin.linear_terms.iter() {
        let mut t = ctx.read_base(*addr, row);
        t.mul_assign(&F::from_u32_with_reduction(*c));
        result.add_assign(&t);
    }
    result
}

/// Resolve a single-column lookup operand `b` (base value), mirroring the IR's
/// `single_column_lookup`: the query is the base linear combination, mapped via
/// the shared lookup resolver.
fn eval_single_column_lookup(
    rel: &NoFieldSingleColumnLookupRelation,
    range_check_width: u32,
    ctx: &RefCtx,
    row: usize,
) -> F {
    let kind = if range_check_width == 16 {
        LookupValueKind::RangeCheck16Index
    } else {
        LookupValueKind::TimestampIndex
    };
    let query = lift(eval_linear(&rel.input, ctx, row));
    ctx.lookup_value(&kind, rel.lookup_set_index, query, row)
}

/// Resolve an alpha-folded vector lookup operand (Ext), mirroring the IR's
/// `folded_lookup`: `Σ_j alpha^j · LookupValue{GenericColumn{j}, set, query_j}`.
fn eval_folded_lookup(rel: &NoFieldVectorLookupRelation, ctx: &RefCtx, row: usize) -> E {
    let mut acc = E::ZERO;
    for (j, column) in rel.columns.iter().enumerate() {
        let query = lift(eval_linear(column, ctx, row));
        let lv = ctx.lookup_value(
            &LookupValueKind::GenericColumn { column: j },
            rel.lookup_set_index,
            query,
            row,
        );
        let mut term = lift(lv);
        if j != 0 {
            term.mul_assign(&ctx.alpha_pow(j as u32));
        }
        acc.add_assign(&term);
    }
    acc
}

/// Resolve an alpha-folded setup operand (Ext): `Σ_j alpha^j · read(cols[j])`.
fn eval_folded_setup(cols: &[GKRAddress], ctx: &RefCtx, row: usize) -> E {
    let mut acc = E::ZERO;
    for (j, addr) in cols.iter().enumerate() {
        let mut term = lift(ctx.read_base(*addr, row));
        if j != 0 {
            term.mul_assign(&ctx.alpha_pow(j as u32));
        }
        acc.add_assign(&term);
    }
    acc
}

#[inline]
fn read_ext(addr: GKRAddress, ctx: &RefCtx, row: usize) -> E {
    lift(ctx.read_base(addr, row))
}

// ── num/den formula helpers (mirror the prover kernels) ─────────────────────

/// PAIR: `num = (b+γ)+(d+γ)`, `den = (b+γ)·(d+γ)`
/// (`lookup_base_pair::pointwise_eval_impl`).
fn pair(b: E, d: E, ctx: &RefCtx) -> [E; 2] {
    let mut sb = b;
    sb.add_assign(&ctx.lookup_additive);
    let mut sd = d;
    sd.add_assign(&ctx.lookup_additive);
    let mut num = sb;
    num.add_assign(&sd);
    let mut den = sb;
    den.mul_assign(&sd);
    [num, den]
}

/// LOOKUP-MINUS-SETUP: `num = (d+γ) − c·(b+γ)`, `den = (b+γ)·(d+γ)`
/// (`lookup_base_minus_multiplicity_base::pointwise_eval_impl`).
fn minus_multiplicity(b: E, c: E, d: E, ctx: &RefCtx) -> [E; 2] {
    let mut sb = b;
    sb.add_assign(&ctx.lookup_additive);
    let mut sd = d;
    sd.add_assign(&ctx.lookup_additive);
    let mut cb = c;
    cb.mul_assign(&sb);
    let mut num = sd;
    num.sub_assign(&cb);
    let mut den = sb;
    den.mul_assign(&sd);
    [num, den]
}

/// DENS-AND-SETUP: `num = a·(d+γ) − c·(b+γ)`, `den = (b+γ)·(d+γ)`
/// (`lookup_pair` rational `a/(b+γ) − c/(d+γ)`).
fn dens_and_setup(a: E, b: E, c: E, d: E, ctx: &RefCtx) -> [E; 2] {
    let mut sb = b;
    sb.add_assign(&ctx.lookup_additive);
    let mut sd = d;
    sd.add_assign(&ctx.lookup_additive);
    let mut a_sd = a;
    a_sd.mul_assign(&sd);
    let mut c_sb = c;
    c_sb.mul_assign(&sb);
    let mut num = a_sd;
    num.sub_assign(&c_sb);
    let mut den = sb;
    den.mul_assign(&sd);
    [num, den]
}

/// UNBALANCED: `num = a·(d+γ) + b`, `den = b·(d+γ)`
/// (`lookup_rational_with_unbalanced_base::pointwise_eval_impl`).
fn unbalanced(a: E, b: E, d: E, ctx: &RefCtx) -> [E; 2] {
    let mut sd = d;
    sd.add_assign(&ctx.lookup_additive);
    let mut num = a;
    num.mul_assign(&sd);
    num.add_assign(&b);
    let mut den = b;
    den.mul_assign(&sd);
    [num, den]
}

/// RATIONAL-PAIR aggregate: `num = a·d + c·b`, `den = b·d` (no γ shift)
/// (`lookup_pair` aggregate `a/b + c/d`).
fn rational_pair(a: E, b: E, c: E, d: E) -> [E; 2] {
    let mut a_d = a;
    a_d.mul_assign(&d);
    let mut c_b = c;
    c_b.mul_assign(&b);
    let mut num = a_d;
    num.add_assign(&c_b);
    let mut den = b;
    den.mul_assign(&d);
    [num, den]
}

// ── memory tuple (mirrors evaluate_memory_query, forward_loop/utils.rs:237) ──

/// The affine memory tuple value (Ext). Independent re-derivation of
/// `evaluate_memory_query`.
fn eval_memory_tuple(rel: &NoFieldSpecialMemoryContributionRelation, ctx: &RefCtx, row: usize) -> E {
    let mut result = ctx.permutation_additive;

    // address space contribution (base, added directly).
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            result.add_assign(&lift(F::from_u32_with_reduction(c)));
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            result.add_assign(&lift(ctx.read_base(GKRAddress::BaseLayerMemory(offset), row)));
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            let mut t = F::ONE;
            t.sub_assign(&ctx.read_base(GKRAddress::BaseLayerMemory(offset), row));
            result.add_assign(&lift(t));
        }
    }

    // address linearization.
    let mem = |col: usize| lift(ctx.read_base(GKRAddress::BaseLayerMemory(col), row));
    let scaled = |slot_idx: usize, inner: E| {
        let mut t = ctx.perm_lin(slot_idx);
        t.mul_assign(&inner);
        t
    };
    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                lift(F::from_u32_with_reduction(*c as u32)),
            ));
        }
        CompiledAddressStrict::Constant(c) => {
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                lift(F::from_u32_with_reduction(*c)),
            ));
        }
        CompiledAddressStrict::U16Space(offset) => {
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                mem(*offset),
            ));
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                mem(*low),
            ));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                mem(*high),
            ));
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            // low limb = mem[low_base] + (low_offset + coeff·mem[dyn]).
            // The prover folds the dynamic term as `as_u32_reduced().wrapping_mul(coeff)`
            // then adds it as a u32 constant; for in-range fixtures this coincides
            // with the field mul (ambiguity-resolution #5).
            let mut low_const = *low_offset;
            if let Some((coeff, dyn_offset)) = *low_dynamic_offset {
                let t = ctx
                    .read_base(GKRAddress::BaseLayerMemory(dyn_offset), row)
                    .as_u32_reduced();
                low_const = low_const.wrapping_add(t.wrapping_mul(coeff as u32));
            }
            let mut low_limb = ctx.read_base(GKRAddress::BaseLayerMemory(*low_base), row);
            low_limb.add_assign(&F::from_u32_with_reduction(low_const));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
                lift(low_limb),
            ));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
                mem(*high),
            ));
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            panic!("U32SpaceGeneric is the confirmed-dead path; no reference value")
        }
    }

    // timestamp.
    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            let mut lo = ctx.read_base(GKRAddress::BaseLayerMemory(ts[0]), row);
            lo.add_assign(&F::from_u32_with_reduction(rel.timestamp_offset as u32));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                lift(lo),
            ));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                mem(ts[1]),
            ));
        }
    }

    // value.
    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(read_value) => {
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                mem(read_value[0]),
            ));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                mem(read_value[1]),
            ));
        }
        RamWordRepresentation::U8Limbs(bytes) => {
            let byte_shift = F::from_u32_with_reduction(1u32 << 8);
            let recompose = |lo_col: usize, hi_col: usize| {
                let mut recomposed = ctx.read_base(GKRAddress::BaseLayerMemory(hi_col), row);
                recomposed.mul_assign(&byte_shift);
                recomposed.add_assign(&ctx.read_base(GKRAddress::BaseLayerMemory(lo_col), row));
                lift(recomposed)
            };
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                recompose(bytes[0], bytes[1]),
            ));
            result.add_assign(&scaled(
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                recompose(bytes[2], bytes[3]),
            ));
        }
    }

    result
}

/// One inits/teardowns RAM tuple (mirrors `evaluate_init` / `evaluate_teardown`,
/// forward_loop/inits_and_teardowns.rs). Address limbs read the virtual setup
/// polys; the high limb adds `set_idx << high_bits_offset` (top_bits convention
/// `top_bits[i] == i`, ambiguity-resolution #4).
fn eval_inits_or_teardowns_tuple(
    ts_and_value: &InitsOrTeardownsTimestampAndValue,
    set_idx: usize,
    is_lhs: bool,
    ctx: &RefCtx,
    row: usize,
) -> E {
    let mut result = ctx.permutation_additive;
    // address space is RAM.
    result.add_assign(&lift(F::from_u32_with_reduction(AddressSpaceType::RAM as u32)));

    // low address.
    let addr_low = ctx.virtual_setup_value(&VirtualSetupKind::InitsAndTeardownsLow, row);
    {
        let mut t = ctx.perm_lin(PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX);
        t.mul_assign(&lift(addr_low));
        result.add_assign(&t);
    }
    // high address = ch · (VirtualSetup(high) + (set_idx << offset)).
    {
        let mut high = ctx.virtual_setup_value(&VirtualSetupKind::InitsAndTeardownsHigh, row);
        let top_bits = (set_idx as u32)
            .checked_shl(ctx.inits_high_bits_offset)
            .unwrap_or(0);
        high.add_assign(&F::from_u32_with_reduction(top_bits));
        let mut t = ctx.perm_lin(PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX);
        t.mul_assign(&lift(high));
        result.add_assign(&t);
    }

    if let InitsOrTeardownsTimestampAndValue::Teardown {
        lhs_timestamp,
        lhs_value,
        rhs_timestamp,
        rhs_value,
    } = ts_and_value
    {
        let (timestamp, value) = if is_lhs {
            (lhs_timestamp, lhs_value)
        } else {
            (rhs_timestamp, rhs_value)
        };
        let mem = |col: usize| lift(ctx.read_base(GKRAddress::BaseLayerMemory(col), row));
        for (idx, col) in [
            (PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, timestamp[0]),
            (PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX, timestamp[1]),
            (PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, value[0]),
            (PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, value[1]),
        ] {
            let mut t = ctx.perm_lin(idx);
            t.mul_assign(&mem(col));
            result.add_assign(&t);
        }
    }

    result
}

/// `constant + Σ_quad c·a·b + Σ_lin c·a` in base (mirrors
/// `EnforceSingleMaxQuadraticConstraintGKRKernel::evaluate_forward` /
/// `MaxQuadratic`). Used for `MaxQuadratic` output AND the constraint vanishing
/// value.
fn eval_max_quadratic(rel: &NoFieldMaxQuadraticGKRRelation, ctx: &RefCtx, row: usize) -> F {
    let mut result = F::from_u32_with_reduction(rel.constant);
    for (a, set) in rel.quadratic_terms.iter() {
        let a_val = ctx.read_base(*a, row);
        for (c, b) in set.iter() {
            let mut t = a_val;
            t.mul_assign(&ctx.read_base(*b, row));
            t.mul_assign(&F::from_u32_with_reduction(*c));
            result.add_assign(&t);
        }
    }
    for (c, a) in rel.linear_terms.iter() {
        let mut t = ctx.read_base(*a, row);
        t.mul_assign(&F::from_u32_with_reduction(*c));
        result.add_assign(&t);
    }
    result
}

/// Batched aggregation `Σ_quad c·rho^p·a·b + Σ_lin c·rho^p·a + Σ_const c·rho^p`
/// in the extension field (mirrors the IR `lower_batched_expr`, which itself
/// follows the companion "Enforce Gates").
fn eval_batched_constraint(
    rel: &NoFieldMaxQuadraticConstraintsGKRRelation,
    ctx: &RefCtx,
    row: usize,
) -> E {
    let mut result = E::ZERO;
    for ((a_addr, b_addr), coeff_powers) in rel.quadratic_terms.iter() {
        let mut ab = ctx.read_base(*a_addr, row);
        ab.mul_assign(&ctx.read_base(*b_addr, row));
        for (c, p) in coeff_powers.iter() {
            let mut term = lift(ab);
            term.mul_assign(&lift(F::from_u32_with_reduction(*c)));
            term.mul_assign(&ctx.rho_pow(*p));
            result.add_assign(&term);
        }
    }
    for (a_addr, coeff_powers) in rel.linear_terms.iter() {
        let a_val = ctx.read_base(*a_addr, row);
        for (c, p) in coeff_powers.iter() {
            let mut term = lift(a_val);
            term.mul_assign(&lift(F::from_u32_with_reduction(*c)));
            term.mul_assign(&ctx.rho_pow(*p));
            result.add_assign(&term);
        }
    }
    for (c, p) in rel.constants.iter() {
        let mut term = lift(F::from_u32_with_reduction(*c));
        term.mul_assign(&ctx.rho_pow(*p));
        result.add_assign(&term);
    }
    result
}

// ── the value oracle: exhaustive per-relation match ─────────────────────────

/// One `Ext` value per claim-bearing output slot, in `RootSlot::Output(i)` /
/// `RootSlot::Constraint(i)` order. EXHAUSTIVE over `NoFieldGKRRelation` — no
/// `_` arm, so a new variant breaks the build (review 4/M completeness).
///
/// Returns `None` ONLY for variants that are genuinely unreferenceable at the
/// value level in this harness; the caller turns a `None` into a TEST FAILURE
/// (no silent skip). Currently every variant returns `Some(..)`.
pub(crate) fn reference_relation_values(
    rel: &NoFieldGKRRelation,
    row: usize,
    ctx: &RefCtx,
) -> Option<Vec<E>> {
    use NoFieldGKRRelation as R;
    let v = match rel {
        // ── arithmetic / copy (single base/ext output) ──
        R::LinearBaseFieldRelation { input, .. } => vec![lift(eval_linear(input, ctx, row))],
        R::MaxQuadratic { input, .. } => vec![lift(eval_max_quadratic(input, ctx, row))],
        R::CopyInBaseField { input, .. } => vec![read_ext(*input, ctx, row)],
        R::CopyInExtensionField { input, .. } => vec![read_ext(*input, ctx, row)],

        // ── single-output lookup materializations ──
        R::MaterializeSingleLookupInput {
            input,
            range_check_width,
            ..
        } => vec![lift(eval_single_column_lookup(input, *range_check_width, ctx, row))],
        R::MaterializedVectorLookupInput { input, .. } => vec![eval_folded_lookup(input, ctx, row)],

        // ── PAIR family: 1/(b+γ) + 1/(d+γ) → [num, den] ──
        R::LookupPairFromBaseInputs {
            input,
            range_check_width,
            ..
        } => {
            let b = lift(eval_single_column_lookup(&input[0], *range_check_width, ctx, row));
            let d = lift(eval_single_column_lookup(&input[1], *range_check_width, ctx, row));
            pair(b, d, ctx).to_vec()
        }
        R::LookupPairFromMaterializedBaseInputs { input, .. } => {
            let b = read_ext(input[0], ctx, row);
            let d = read_ext(input[1], ctx, row);
            pair(b, d, ctx).to_vec()
        }
        R::LookupPairFromVectorInputs { input, .. } => {
            let b = eval_folded_lookup(&input[0], ctx, row);
            let d = eval_folded_lookup(&input[1], ctx, row);
            pair(b, d, ctx).to_vec()
        }
        R::LookupPairFromMaterializedVectorInputs { input, .. }
        | R::LookupPairFromCachedVectorInputs { input, .. } => {
            let b = read_ext(input[0], ctx, row);
            let d = read_ext(input[1], ctx, row);
            pair(b, d, ctx).to_vec()
        }

        // ── LOOKUP-MINUS-SETUP: 1/(b+γ) − c/(d+γ) ──
        R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. }
        | R::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
            let b = read_ext(*input, ctx, row);
            let c = read_ext(setup[0], ctx, row);
            let d = read_ext(setup[1], ctx, row);
            minus_multiplicity(b, c, d, ctx).to_vec()
        }
        R::LookupFromVectorInputWithSetup { input, setup, .. } => {
            let b = eval_folded_lookup(input, ctx, row);
            let c = read_ext(setup.0, ctx, row);
            let d = eval_folded_setup(&setup.1, ctx, row);
            minus_multiplicity(b, c, d, ctx).to_vec()
        }

        // ── DENS-AND-SETUP: a/(b+γ) − c/(d+γ) ──
        R::LookupWithCachedDensAndSetup { input, setup, .. } => {
            let a = read_ext(input[0], ctx, row);
            let b = read_ext(input[1], ctx, row);
            let c = read_ext(setup[0], ctx, row);
            let d = read_ext(setup[1], ctx, row);
            dens_and_setup(a, b, c, d, ctx).to_vec()
        }
        R::LookupWithDensAndSetupExpressions { input, setup, .. } => {
            let a = read_ext(input.0, ctx, row);
            let b = eval_folded_lookup(&input.1, ctx, row);
            let c = read_ext(setup.0, ctx, row);
            let d = eval_folded_setup(&setup.1, ctx, row);
            dens_and_setup(a, b, c, d, ctx).to_vec()
        }
        R::LookupWithDensAndCachedSetup { input, setup, .. } => {
            let a = read_ext(input.0, ctx, row);
            let b = eval_folded_lookup(&input.1, ctx, row);
            let c = read_ext(setup.0, ctx, row);
            let d = read_ext(setup.1, ctx, row);
            dens_and_setup(a, b, c, d, ctx).to_vec()
        }

        // ── UNBALANCED: a/b + 1/(d+γ) ──
        R::LookupUnbalancedPairWithMaterializedBaseInputs {
            input, remainder, ..
        }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs {
            input, remainder, ..
        } => {
            let a = read_ext(input[0], ctx, row);
            let b = read_ext(input[1], ctx, row);
            let d = read_ext(*remainder, ctx, row);
            unbalanced(a, b, d, ctx).to_vec()
        }
        R::LookupUnbalancedPairWithVectorInputs {
            input, remainder, ..
        } => {
            let a = read_ext(input[0], ctx, row);
            let b = read_ext(input[1], ctx, row);
            let d = eval_folded_lookup(remainder, ctx, row);
            unbalanced(a, b, d, ctx).to_vec()
        }

        // ── RATIONAL-PAIR aggregate: a/b + c/d ──
        R::AggregateLookupRationalPair { input, .. } => {
            let a = read_ext(input[0][0], ctx, row);
            let b = read_ext(input[0][1], ctx, row);
            let c = read_ext(input[1][0], ctx, row);
            let d = read_ext(input[1][1], ctx, row);
            rational_pair(a, b, c, d).to_vec()
        }

        // ── grand-product / product / mask (single Ext output) ──
        R::InitialGrandProductFromCaches { input, .. }
        | R::TrivialProduct { input, .. } => {
            let mut p = read_ext(input[0], ctx, row);
            p.mul_assign(&read_ext(input[1], ctx, row));
            vec![p]
        }
        R::UnbalancedGrandProductWithCache { scalar, input, .. } => {
            let mut p = read_ext(*scalar, ctx, row);
            p.mul_assign(&read_ext(*input, ctx, row));
            vec![p]
        }
        R::InitialGrandProductWithoutCaches { input, .. } => {
            let mut p = eval_memory_tuple(&input[0], ctx, row);
            p.mul_assign(&eval_memory_tuple(&input[1], ctx, row));
            vec![p]
        }
        R::MaterializeGrandProductTermExpression { input, .. } => {
            vec![eval_memory_tuple(input, ctx, row)]
        }
        R::MaskIntoIdentityProduct { input, mask, .. } => {
            // 1 + mask·(input − 1).
            let input_v = read_ext(*input, ctx, row);
            let mask_v = read_ext(*mask, ctx, row);
            let mut input_minus_one = input_v;
            input_minus_one.sub_assign(&lift(F::ONE));
            let mut masked = mask_v;
            masked.mul_assign(&input_minus_one);
            let mut result = lift(F::ONE);
            result.add_assign(&masked);
            vec![result]
        }

        // ── inits / teardowns (product of two RAM tuples) ──
        R::InitsOrTeardownsInitialPair {
            timestamp_and_value,
            set_idxes,
            ..
        } => {
            let lhs = eval_inits_or_teardowns_tuple(
                timestamp_and_value,
                set_idxes[0],
                /* is_lhs */ true,
                ctx,
                row,
            );
            let rhs = eval_inits_or_teardowns_tuple(
                timestamp_and_value,
                set_idxes[1],
                /* is_lhs */ false,
                ctx,
                row,
            );
            let mut p = lhs;
            p.mul_assign(&rhs);
            vec![p]
        }

        // ── enforce / constraint family (Constraint roots) ──
        R::EnforceSingleMaxQuadraticConstraint { input, .. } => {
            vec![lift(eval_max_quadratic(input, ctx, row))]
        }
        R::EnforceConstraintsMaxQuadratic { input } => {
            vec![eval_batched_constraint(input, ctx, row)]
        }
    };
    Some(v)
}

// ── address collection (exhaustive over all variants) ───────────────────────

fn collect_linear(lin: &NoFieldLinearRelation, out: &mut BTreeSet<GKRAddress>) {
    for (_, a) in lin.linear_terms.iter() {
        out.insert(*a);
    }
}

fn collect_scl(scl: &NoFieldSingleColumnLookupRelation, out: &mut BTreeSet<GKRAddress>) {
    collect_linear(&scl.input, out);
}

fn collect_vector(vl: &NoFieldVectorLookupRelation, out: &mut BTreeSet<GKRAddress>) {
    for col in vl.columns.iter() {
        collect_linear(col, out);
    }
}

fn collect_mem(rel: &NoFieldSpecialMemoryContributionRelation, out: &mut BTreeSet<GKRAddress>) {
    let m = |c: usize| GKRAddress::BaseLayerMemory(c);
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(_) => {}
        CompiledAddressSpaceRelationStrict::IsRam(o)
        | CompiledAddressSpaceRelationStrict::IsRegister(o) => {
            out.insert(m(o));
        }
    }
    match &rel.address {
        CompiledAddressStrict::ConstantU16(_) | CompiledAddressStrict::Constant(_) => {}
        CompiledAddressStrict::U16Space(o) => {
            out.insert(m(*o));
        }
        CompiledAddressStrict::U32Space([lo, hi]) => {
            out.insert(m(*lo));
            out.insert(m(*hi));
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            high,
            ..
        } => {
            out.insert(m(*low_base));
            out.insert(m(*high));
            if let Some((_, dyn_off)) = low_dynamic_offset {
                out.insert(m(*dyn_off));
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {}
    }
    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            out.insert(m(ts[0]));
            out.insert(m(ts[1]));
        }
    }
    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(v) => {
            out.insert(m(v[0]));
            out.insert(m(v[1]));
        }
        RamWordRepresentation::U8Limbs(b) => {
            for c in b.iter() {
                out.insert(m(*c));
            }
        }
    }
}

/// Collect every base/setup/virtual-setup address a relation reads, so `RefCtx`
/// can bind a value for each. EXHAUSTIVE — no `_` arm.
pub(crate) fn collect_addresses(rel: &NoFieldGKRRelation, out: &mut BTreeSet<GKRAddress>) {
    use NoFieldGKRRelation as R;
    match rel {
        R::LinearBaseFieldRelation { input, .. } => collect_linear(input, out),
        R::MaxQuadratic { input, .. } | R::EnforceSingleMaxQuadraticConstraint { input, .. } => {
            for (a, set) in input.quadratic_terms.iter() {
                out.insert(*a);
                for (_, b) in set.iter() {
                    out.insert(*b);
                }
            }
            for (_, a) in input.linear_terms.iter() {
                out.insert(*a);
            }
        }
        R::EnforceConstraintsMaxQuadratic { input } => {
            for ((a, b), _) in input.quadratic_terms.iter() {
                out.insert(*a);
                out.insert(*b);
            }
            for (a, _) in input.linear_terms.iter() {
                out.insert(*a);
            }
        }
        R::CopyInBaseField { input, .. } | R::CopyInExtensionField { input, .. } => {
            out.insert(*input);
        }
        R::MaterializeSingleLookupInput { input, .. } => collect_scl(input, out),
        R::MaterializedVectorLookupInput { input, .. } => collect_vector(input, out),
        R::LookupPairFromBaseInputs { input, .. } => {
            collect_scl(&input[0], out);
            collect_scl(&input[1], out);
        }
        R::LookupPairFromMaterializedBaseInputs { input, .. }
        | R::LookupPairFromMaterializedVectorInputs { input, .. }
        | R::LookupPairFromCachedVectorInputs { input, .. }
        | R::InitialGrandProductFromCaches { input, .. }
        | R::TrivialProduct { input, .. } => {
            out.insert(input[0]);
            out.insert(input[1]);
        }
        R::LookupPairFromVectorInputs { input, .. } => {
            collect_vector(&input[0], out);
            collect_vector(&input[1], out);
        }
        R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. }
        | R::LookupFromMaterializedVectorInputWithSetup { input, setup, .. } => {
            out.insert(*input);
            out.insert(setup[0]);
            out.insert(setup[1]);
        }
        R::LookupFromVectorInputWithSetup { input, setup, .. } => {
            collect_vector(input, out);
            out.insert(setup.0);
            for a in setup.1.iter() {
                out.insert(*a);
            }
        }
        R::LookupWithCachedDensAndSetup { input, setup, .. } => {
            out.insert(input[0]);
            out.insert(input[1]);
            out.insert(setup[0]);
            out.insert(setup[1]);
        }
        R::LookupWithDensAndSetupExpressions { input, setup, .. } => {
            out.insert(input.0);
            collect_vector(&input.1, out);
            out.insert(setup.0);
            for a in setup.1.iter() {
                out.insert(*a);
            }
        }
        R::LookupWithDensAndCachedSetup { input, setup, .. } => {
            out.insert(input.0);
            collect_vector(&input.1, out);
            out.insert(setup.0);
            out.insert(setup.1);
        }
        R::LookupUnbalancedPairWithMaterializedBaseInputs { input, remainder, .. }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs { input, remainder, .. } => {
            out.insert(input[0]);
            out.insert(input[1]);
            out.insert(*remainder);
        }
        R::LookupUnbalancedPairWithVectorInputs { input, remainder, .. } => {
            out.insert(input[0]);
            out.insert(input[1]);
            collect_vector(remainder, out);
        }
        R::AggregateLookupRationalPair { input, .. } => {
            for pair in input.iter() {
                out.insert(pair[0]);
                out.insert(pair[1]);
            }
        }
        R::InitialGrandProductWithoutCaches { input, .. } => {
            collect_mem(&input[0], out);
            collect_mem(&input[1], out);
        }
        R::UnbalancedGrandProductWithCache { scalar, input, .. } => {
            out.insert(*scalar);
            out.insert(*input);
        }
        R::MaterializeGrandProductTermExpression { input, .. } => collect_mem(input, out),
        R::MaskIntoIdentityProduct { input, mask, .. } => {
            out.insert(*input);
            out.insert(*mask);
        }
        R::InitsOrTeardownsInitialPair {
            timestamp_and_value,
            ..
        } => {
            // virtual setups are bound separately (resolver-side); only memory
            // limb reads come from storage (teardown only).
            if let InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp,
                lhs_value,
                rhs_timestamp,
                rhs_value,
            } = timestamp_and_value
            {
                for c in lhs_timestamp.iter().chain(rhs_timestamp.iter()) {
                    out.insert(GKRAddress::BaseLayerMemory(*c));
                }
                for c in lhs_value.iter().chain(rhs_value.iter()) {
                    out.insert(GKRAddress::BaseLayerMemory(*c));
                }
            }
        }
    }
}

// ── resolvers bound to the SAME RefCtx ──────────────────────────────────────

pub(crate) struct StorageReadResolver<'a> {
    pub ctx: &'a RefCtx,
}
impl<'a> ReadResolver for StorageReadResolver<'a> {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        lift(self.ctx.read_base(read_place_to_address(place), row))
    }
}

/// Map a `ReadPlace` back to the `GKRAddress` whose value `RefCtx` bound. The
/// inverse of `dag_ir::lower::map_address` for the base/inner/cache/setup places.
pub(crate) fn read_place_to_address(place: &ReadPlace) -> GKRAddress {
    match place {
        ReadPlace::BaseLayerWitness { column } => GKRAddress::BaseLayerWitness(*column),
        ReadPlace::BaseLayerMemory { column } => GKRAddress::BaseLayerMemory(*column),
        ReadPlace::Setup { column } => GKRAddress::Setup(*column),
        ReadPlace::LayerOutput { layer, offset } => GKRAddress::InnerLayer {
            layer: *layer,
            offset: *offset,
        },
        ReadPlace::CacheOutput { layer, offset } => GKRAddress::Cached {
            layer: *layer,
            offset: *offset,
        },
        ReadPlace::Scratch { .. } => {
            panic!("ReadPlace::Scratch has no bound base value in the differential harness")
        }
    }
}

pub(crate) struct RefLookupResolver<'a> {
    pub ctx: &'a RefCtx,
}
impl<'a> LookupResolver for RefLookupResolver<'a> {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        self.ctx.lookup_value(kind, set_index, evaluated_query, row)
    }
}

pub(crate) struct RefVirtualSetupResolver<'a> {
    pub ctx: &'a RefCtx,
}
impl<'a> VirtualSetupResolver for RefVirtualSetupResolver<'a> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        self.ctx.virtual_setup_value(kind, row)
    }
}

pub(crate) struct RefChallengeResolver<'a> {
    pub ctx: &'a RefCtx,
}
impl<'a> ChallengeResolver for RefChallengeResolver<'a> {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        self.ctx.challenge(r)
    }
}
