//! Memory-tuple / grand-product / mask / inits-teardowns lowering for the DAG IR.
//!
//! A memory tuple is NOT a source in this design: it lowers to an affine `Expr`
//! over `Read(BaseLayerMemory)` leaves, base-field constants, and permutation
//! challenges. The authoritative arithmetic is `evaluate_memory_query` in
//! `prover/src/gkr/prover/forward_loop/utils.rs`, which turns a
//! `NoFieldSpecialMemoryContributionRelation` into:
//!
//! ```text
//! tuple = Challenge(PermutationAdditive)
//!       + address_space_contribution
//!       + Σ_slot Challenge(PermutationLinearization(slot)) · limb_or_offset
//! ```
//!
//! Descriptor special cases (local arithmetic rewrites, per the companion doc
//! "Memory Tuple Gates"):
//!
//! - address space `Constant(c)` → `c`; `IsRam(bit)` → `bit`; `IsRegister(bit)` → `1 − bit`
//! - address `ConstantU16(c)`/`Constant(c)` → `ch(AddressLow)·c`
//! - address `U16Space(o)` → `ch(AddressLow)·mem[o]`
//! - address `U32Space([lo,hi])` → `ch(AddressLow)·mem[lo] + ch(AddressHigh)·mem[hi]`
//! - address `U32SpaceSpecialIndirect` → `ch(AddressLow)·(mem[low_base] + low_offset
//!       + coeff·mem[dynamic]) + ch(AddressHigh)·mem[high]`
//! - timestamp `Normal([lo,hi])` → `ch(TsLow)·(mem[lo] + timestamp_offset) + ch(TsHigh)·mem[hi]`
//! - value `U16Limbs([lo,hi])` → `ch(ValLow)·mem[lo] + ch(ValHigh)·mem[hi]`
//! - value `U8Limbs([b0,b1,b2,b3])` → `ch(ValLow)·(mem[b0] + 2^8·mem[b1])
//!       + ch(ValHigh)·(mem[b2] + 2^8·mem[b3])`
//! - `Zero` timestamp/value/`U32SpaceGeneric` address → see below.
//!
//! `U32SpaceGeneric` is the confirmed-dead path (the prover's `evaluate_memory_query`
//! `todo!()`s on it); we return `Err(...)` rather than lowering it. Task 14 audits
//! that no golden artifact contains it.
//!
//! Subtraction never appears here, so there is no `Sub`/`Neg` node; the only
//! signed term is the U8 byte shift `2^8`, a plain positive base constant.

use crate::definitions::{
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
};
use crate::definitions::gkr::{AddressSpaceType, RamWordRepresentation};
use crate::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    InitsOrTeardownsTimestampAndValue, NoFieldSpecialMemoryContributionRelation,
};

use super::super::{
    ArenaBuilder, ChallengeKey, ChallengePower, ChallengeRef, ExprId, PermutationSlot, ReadPlace,
    SourceKind,
};

/// `2^8`, the byte shift for `U8Limbs` value recomposition (`b_lo + 2^8·b_hi`).
const BYTE_SHIFT: u32 = 1 << 8;

// ── primitive builders ─────────────────────────────────────────────────────────

/// `Read(BaseLayerMemory { column })` as an `ExprId`.
fn mem_read(arena: &mut ArenaBuilder, column: usize) -> ExprId {
    let src = arena.intern_source(SourceKind::Read {
        place: ReadPlace::BaseLayerMemory { column },
    });
    arena.source_expr(src)
}

/// A base-field `Constant`.
fn constant(arena: &mut ArenaBuilder, value: u32) -> ExprId {
    let src = arena.intern_source(SourceKind::Constant { value });
    arena.source_expr(src)
}

/// `Challenge(PermutationAdditive, One)`.
fn permutation_additive(arena: &mut ArenaBuilder) -> ExprId {
    let src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef {
            key: ChallengeKey::PermutationAdditive,
            power: ChallengePower::One,
        },
    });
    arena.source_expr(src)
}

/// `Challenge(PermutationLinearization(slot), One)`.
fn permutation_linearization(arena: &mut ArenaBuilder, slot: PermutationSlot) -> ExprId {
    let src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef {
            key: ChallengeKey::PermutationLinearization(slot),
            power: ChallengePower::One,
        },
    });
    arena.source_expr(src)
}

/// The `PermutationSlot` for a permutation linearization challenge-power index.
///
/// Maps the prover's flat challenge-power layout (`*_IDX` constants in
/// `definitions::constants`) onto the typed DAG-IR slot enum. Only the address
/// slots are used by name elsewhere; the rest are interned through the explicit
/// `PermutationSlot::*` calls in this module.
fn slot_for_address_low() -> PermutationSlot {
    debug_assert_eq!(PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, 0);
    PermutationSlot::AddressLow
}

fn slot_for_address_high() -> PermutationSlot {
    debug_assert_eq!(PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, 1);
    PermutationSlot::AddressHigh
}

// ── memory tuple ────────────────────────────────────────────────────────────────

/// Lower a `NoFieldSpecialMemoryContributionRelation` into an affine `Expr`,
/// matching `evaluate_memory_query`.
///
/// Returns `Err` only for the confirmed-dead `U32SpaceGeneric` address form.
///
/// `minus_one` is the reduced base-field `−1` (`F::CHARACTERISTICS − 1`), used to
/// encode the `IsRegister` `1 − bit` rewrite without a `Sub`/`Neg` node.
pub(super) fn lower_memory_tuple(
    arena: &mut ArenaBuilder,
    rel: &NoFieldSpecialMemoryContributionRelation,
    minus_one: u32,
) -> Result<ExprId, String> {
    let mut terms: Vec<ExprId> = Vec::with_capacity(8);

    // result starts at the additive permutation challenge.
    terms.push(permutation_additive(arena));

    // address-space contribution (base-valued, added directly).
    terms.push(address_space_term(arena, &rel.address_space, minus_one));

    // address contribution (ch(AddressLow/High) · limb).
    address_terms(arena, &rel.address, &mut terms)?;

    // timestamp contribution.
    timestamp_terms(arena, &rel.timestamp, rel.timestamp_offset, &mut terms);

    // value contribution.
    value_terms(arena, &rel.value, &mut terms);

    Ok(arena.add(terms))
}

/// Address-space contribution: `Constant(c) → c`, `IsRam(bit) → bit`,
/// `IsRegister(bit) → 1 − bit` (encoded as `1 + (CHARACTERISTICS−1)·bit`).
fn address_space_term(
    arena: &mut ArenaBuilder,
    space: &CompiledAddressSpaceRelationStrict,
    minus_one: u32,
) -> ExprId {
    match space {
        CompiledAddressSpaceRelationStrict::Constant(c) => constant(arena, *c),
        CompiledAddressSpaceRelationStrict::IsRam(offset) => mem_read(arena, *offset),
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            // 1 − bit, the register indicator.
            let one = constant(arena, 1);
            let bit = mem_read(arena, *offset);
            let neg_bit = scale_minus_one(arena, bit, minus_one);
            arena.add(vec![one, neg_bit])
        }
    }
}

/// `(CHARACTERISTICS − 1) · term`, i.e. `−term`, encoded without a `Neg` node.
fn scale_minus_one(arena: &mut ArenaBuilder, term: ExprId, minus_one: u32) -> ExprId {
    let neg = constant(arena, minus_one);
    arena.mul(vec![neg, term])
}

/// `ch(slot) · inner`.
fn challenge_scaled(arena: &mut ArenaBuilder, slot: PermutationSlot, inner: ExprId) -> ExprId {
    let ch = permutation_linearization(arena, slot);
    arena.mul(vec![ch, inner])
}

/// Append the address linearization terms; `Err` for `U32SpaceGeneric`.
fn address_terms(
    arena: &mut ArenaBuilder,
    address: &CompiledAddressStrict,
    terms: &mut Vec<ExprId>,
) -> Result<(), String> {
    match address {
        CompiledAddressStrict::ConstantU16(c) => {
            let lo = constant(arena, *c as u32);
            terms.push(challenge_scaled(arena, slot_for_address_low(), lo));
        }
        CompiledAddressStrict::Constant(c) => {
            let lo = constant(arena, *c);
            terms.push(challenge_scaled(arena, slot_for_address_low(), lo));
        }
        CompiledAddressStrict::U16Space(offset) => {
            let lo = mem_read(arena, *offset);
            terms.push(challenge_scaled(arena, slot_for_address_low(), lo));
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            let lo = mem_read(arena, *low);
            terms.push(challenge_scaled(arena, slot_for_address_low(), lo));
            let hi = mem_read(arena, *high);
            terms.push(challenge_scaled(arena, slot_for_address_high(), hi));
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            // low limb = mem[low_base] + low_offset (+ coeff·mem[dynamic]).
            let mut low_parts = Vec::with_capacity(3);
            low_parts.push(mem_read(arena, *low_base));
            if *low_offset != 0 {
                low_parts.push(constant(arena, *low_offset));
            }
            if let Some((coeff, dyn_offset)) = low_dynamic_offset {
                let dyn_read = mem_read(arena, *dyn_offset);
                let scaled = {
                    let c = constant(arena, *coeff as u32);
                    arena.mul(vec![c, dyn_read])
                };
                low_parts.push(scaled);
            }
            let low_limb = arena.add(low_parts);
            terms.push(challenge_scaled(arena, slot_for_address_low(), low_limb));

            let hi = mem_read(arena, *high);
            terms.push(challenge_scaled(arena, slot_for_address_high(), hi));
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            return Err(
                "dag_ir: U32SpaceGeneric address form is the confirmed-dead path and is not lowered \
                 (Task 14 audits its absence)"
                    .to_string(),
            );
        }
    }
    Ok(())
}

/// Append the timestamp linearization terms. `Normal([lo, hi])` adds
/// `ch(TsLow)·(mem[lo] + timestamp_offset) + ch(TsHigh)·mem[hi]`; `Zero` adds nothing.
fn timestamp_terms(
    arena: &mut ArenaBuilder,
    timestamp: &CompiledMemoryTimestamp,
    timestamp_offset: u32,
    terms: &mut Vec<ExprId>,
) {
    match timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(ts) => {
            // low limb carries the constant timestamp offset.
            let lo_read = mem_read(arena, ts[0]);
            let lo_inner = if timestamp_offset != 0 {
                let off = constant(arena, timestamp_offset);
                arena.add(vec![lo_read, off])
            } else {
                lo_read
            };
            terms.push(challenge_scaled(arena, PermutationSlot::TimestampLow, lo_inner));

            let hi = mem_read(arena, ts[1]);
            terms.push(challenge_scaled(arena, PermutationSlot::TimestampHigh, hi));
        }
    }
}

/// Append the value linearization terms. `U16Limbs` reads two limbs directly;
/// `U8Limbs` recomposes each limb as `b_lo + 2^8·b_hi`; `Zero` adds nothing.
fn value_terms(
    arena: &mut ArenaBuilder,
    value: &RamWordRepresentation,
    terms: &mut Vec<ExprId>,
) {
    match value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(read_value) => {
            let lo = mem_read(arena, read_value[0]);
            terms.push(challenge_scaled(arena, PermutationSlot::ValueLow, lo));
            let hi = mem_read(arena, read_value[1]);
            terms.push(challenge_scaled(arena, PermutationSlot::ValueHigh, hi));
        }
        RamWordRepresentation::U8Limbs(bytes) => {
            // value_low = bytes[0] + 2^8·bytes[1]; value_high = bytes[2] + 2^8·bytes[3].
            let lo = recompose_bytes(arena, bytes[0], bytes[1]);
            terms.push(challenge_scaled(arena, PermutationSlot::ValueLow, lo));
            let hi = recompose_bytes(arena, bytes[2], bytes[3]);
            terms.push(challenge_scaled(arena, PermutationSlot::ValueHigh, hi));
        }
    }
}

/// `mem[lo] + 2^8·mem[hi]` — one 16-bit limb recomposed from two bytes.
fn recompose_bytes(arena: &mut ArenaBuilder, lo_col: usize, hi_col: usize) -> ExprId {
    let lo = mem_read(arena, lo_col);
    let hi = mem_read(arena, hi_col);
    let shift = constant(arena, BYTE_SHIFT);
    let hi_shifted = arena.mul(vec![shift, hi]);
    arena.add(vec![lo, hi_shifted])
}

// ── grand-product / product / mask ──────────────────────────────────────────────

/// `read(a) · read(b)` for grand-product gates whose operands are prior Ext
/// reads (addresses), via [`super::map_address`].
pub(super) fn product_of_reads(
    arena: &mut ArenaBuilder,
    a: crate::definitions::GKRAddress,
    b: crate::definitions::GKRAddress,
) -> ExprId {
    let a = read_addr(arena, a);
    let b = read_addr(arena, b);
    arena.mul(vec![a, b])
}

/// `lower_memory_tuple(a) · lower_memory_tuple(b)`.
pub(super) fn product_of_tuples(
    arena: &mut ArenaBuilder,
    a: &NoFieldSpecialMemoryContributionRelation,
    b: &NoFieldSpecialMemoryContributionRelation,
    minus_one: u32,
) -> Result<ExprId, String> {
    let a = lower_memory_tuple(arena, a, minus_one)?;
    let b = lower_memory_tuple(arena, b, minus_one)?;
    Ok(arena.mul(vec![a, b]))
}

/// `Read`/`Prior` of `addr` (same-layer cache addresses alias via `Prior`; see
/// [`super::util::read_source`]).
fn read_addr(arena: &mut ArenaBuilder, addr: crate::definitions::GKRAddress) -> ExprId {
    let src = arena.intern_source(super::util::read_source(arena, addr));
    arena.source_expr(src)
}

/// `MaskIntoIdentityProduct`: `1 + mask·(input − 1)` (equivalently
/// `input·mask + (1 − mask)`). `input − 1` is `input + (−1)`.
pub(super) fn mask_into_identity(
    arena: &mut ArenaBuilder,
    input: crate::definitions::GKRAddress,
    mask: crate::definitions::GKRAddress,
    minus_one: u32,
) -> ExprId {
    let input = read_addr(arena, input);
    let mask = read_addr(arena, mask);
    let one = constant(arena, 1);
    // input − 1
    let neg_one = constant(arena, minus_one);
    let input_minus_one = arena.add(vec![input, neg_one]);
    // mask · (input − 1)
    let masked = arena.mul(vec![mask, input_minus_one]);
    // 1 + mask·(input − 1)
    arena.add(vec![one, masked])
}

// ── inits / teardowns ────────────────────────────────────────────────────────────

/// Lower `InitsOrTeardownsInitialPair` into the product of two RAM tuples.
///
/// Both tuples have:
/// - address space = `RAM` (the base-field constant `AddressSpaceType::RAM`)
/// - low address  = `ch(AddressLow)·VirtualSetup(InitsAndTeardownsLow)`
/// - high address = `ch(AddressHigh)·(VirtualSetup(InitsAndTeardownsHigh) + top_bits_const)`
///
/// The `Init` arm has zero timestamp and value (no extra terms); the `Teardown`
/// arm adds `ch(TsLow/High)·mem[ts]` and `ch(ValLow/High)·mem[val]` limb reads.
///
/// `top_bits_const(set_idx) = inits_and_teardowns_top_bits[set_idx] << high_bits_offset`
/// with `high_bits_offset = log2(trace_len) + WORD_BITS − 16`. See [`top_bits_const`]
/// for the runtime-array caveat.
pub(super) fn lower_inits_or_teardowns(
    arena: &mut ArenaBuilder,
    timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
    set_idxes: [usize; 2],
    trace_len: usize,
    word_bits: Option<u32>,
) -> ExprId {
    let lhs = inits_or_teardowns_tuple(
        arena,
        timestamp_and_value,
        set_idxes[0],
        trace_len,
        word_bits,
        /* is_lhs */ true,
    );
    let rhs = inits_or_teardowns_tuple(
        arena,
        timestamp_and_value,
        set_idxes[1],
        trace_len,
        word_bits,
        /* is_lhs */ false,
    );
    arena.mul(vec![lhs, rhs])
}

/// Build one inits/teardowns tuple for a single `set_idx`.
fn inits_or_teardowns_tuple(
    arena: &mut ArenaBuilder,
    timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
    set_idx: usize,
    trace_len: usize,
    word_bits: Option<u32>,
    is_lhs: bool,
) -> ExprId {
    let mut terms: Vec<ExprId> = Vec::with_capacity(6);

    // additive permutation challenge.
    terms.push(permutation_additive(arena));

    // address space is RAM (a base-field constant).
    terms.push(constant(arena, AddressSpaceType::RAM as u32));

    // low address: ch(AddressLow) · VirtualSetup(InitsAndTeardownsLow).
    let addr_low = virtual_setup(arena, super::super::VirtualSetupKind::InitsAndTeardownsLow);
    terms.push(challenge_scaled(arena, slot_for_address_low(), addr_low));

    // high address: ch(AddressHigh) · (VirtualSetup(InitsAndTeardownsHigh) + top_bits).
    let addr_high_setup =
        virtual_setup(arena, super::super::VirtualSetupKind::InitsAndTeardownsHigh);
    let top_bits = top_bits_const(set_idx, trace_len, word_bits);
    let addr_high_inner = if top_bits != 0 {
        let top = constant(arena, top_bits);
        arena.add(vec![addr_high_setup, top])
    } else {
        addr_high_setup
    };
    terms.push(challenge_scaled(arena, slot_for_address_high(), addr_high_inner));

    // timestamp + value limbs (Teardown only; Init contributes zero).
    if let InitsOrTeardownsTimestampAndValue::Teardown {
        lhs_timestamp,
        lhs_value,
        rhs_timestamp,
        rhs_value,
    } = timestamp_and_value
    {
        let (timestamp, value) = if is_lhs {
            (lhs_timestamp, lhs_value)
        } else {
            (rhs_timestamp, rhs_value)
        };
        let ts_lo = mem_read(arena, timestamp[0]);
        terms.push(challenge_scaled(arena, PermutationSlot::TimestampLow, ts_lo));
        let ts_hi = mem_read(arena, timestamp[1]);
        terms.push(challenge_scaled(arena, PermutationSlot::TimestampHigh, ts_hi));
        let val_lo = mem_read(arena, value[0]);
        terms.push(challenge_scaled(arena, PermutationSlot::ValueLow, val_lo));
        let val_hi = mem_read(arena, value[1]);
        terms.push(challenge_scaled(arena, PermutationSlot::ValueHigh, val_hi));
    }

    arena.add(terms)
}

/// `VirtualSetup(kind)` as an `ExprId`.
fn virtual_setup(arena: &mut ArenaBuilder, kind: super::super::VirtualSetupKind) -> ExprId {
    let src = arena.intern_source(SourceKind::VirtualSetup { kind });
    arena.source_expr(src)
}

/// `inits_and_teardowns_top_bits[set_idx] << high_bits_offset`.
///
/// `high_bits_offset = log2(trace_len) + WORD_BITS − 16`.
///
/// CAVEAT: the runtime `inits_and_teardowns_top_bits` array is a prover argument
/// that is NOT present in `GKRCircuitArtifact`. The compiler/prover convention
/// (confirmed in `prover/.../family_circuits.rs` and the kernel-collector launch
/// path) is `inits_and_teardowns_top_bits[i] == i`, so we resolve the top bits to
/// `set_idx` directly. If `word_bits` is absent (it is `Option<u32>` on the memory
/// layout and `None` in synthetic fixtures), `high_bits_offset` cannot be computed,
/// so the shift is skipped (offset 0). Value-correctness of this constant is a
/// Task-13 prover concern; this lowering only fixes the SHAPE.
fn top_bits_const(set_idx: usize, trace_len: usize, word_bits: Option<u32>) -> u32 {
    let top_bits = set_idx as u32;
    match word_bits {
        Some(word_bits) if trace_len.is_power_of_two() && trace_len > 0 => {
            let log2_trace_len = trace_len.trailing_zeros();
            // high_bits_offset = log2(trace_len) + WORD_BITS − 16; saturate to avoid
            // underflow/overflow on synthetic inputs that violate the real-circuit
            // invariant (log2_trace_len + WORD_BITS ≥ 16).
            let shift = (log2_trace_len + word_bits).saturating_sub(16);
            top_bits.checked_shl(shift).unwrap_or(0)
        }
        _ => top_bits,
    }
}
