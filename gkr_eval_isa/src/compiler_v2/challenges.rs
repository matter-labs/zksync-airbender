//! Challenge-bank classification by TRANSFER CHANNEL (spec §5). All forward
//! challenges are per-proof Fiat-Shamir outputs; the axis is where the value
//! is materialized: α/γ are device-squeezed (`ConstChallenge`, __constant__),
//! perm/additive are host-drawn at schedule time (`ArgChallenge`, kernel-arg).
//! α enters as a COLUMN-INDEXED power bank (acc = Σ α^k·col_k), never raised
//! per-step; γ as [γ, γ², 2γ].

use crate::isa_v2::LdcSub;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeFamily {
    Alpha,
    Gamma,
    PermLinearization,
    AdditiveSeed,
}

pub fn bank_for_family(f: ChallengeFamily) -> LdcSub {
    match f {
        ChallengeFamily::Alpha | ChallengeFamily::Gamma => LdcSub::ConstChallenge,
        ChallengeFamily::PermLinearization | ChallengeFamily::AdditiveSeed => LdcSub::ArgChallenge,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlphaSlot {
    /// col_0: α^0 = 1, multiply-free lift — no bank read needed.
    OneLift,
    /// col_k (k > 0): read bank entry k for α^k.
    Power(u16),
}

pub fn alpha_power_bank_index(col_k: u16) -> AlphaSlot {
    if col_k == 0 {
        AlphaSlot::OneLift
    } else {
        AlphaSlot::Power(col_k)
    }
}

// R2 (Phase 2.5): v2 lowering needs a SUPERSET of v1's arena-only const table
// (it must also recover the cache coefficients/constants + memory-tuple folded
// constants as `Ldc` lanes), so it uses `build_const_table_v2` below rather than
// re-exporting v1's `compiler::build_const_table`. v1's dedup convention (sorted,
// deduped, 0/1/NEG_ONE_U32 excluded) is preserved verbatim in `build_const_table_v2`.
// NOTE (F4): the v1 fn is `pub(crate)`; any in-crate reference must be by path or
// `pub(crate) use` (never `pub use` — E0364). v1 behaviour is NOT changed by R2.

use crate::isa::NEG_ONE_U32;
use cs::gkr_compiler::codegen_ir::{CacheKind, CodegenLayer, ExprNode, LinearComb};
use cs::gkr_compiler::{CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp};

/// R2 (Phase 2.5): a base-field scalar must ride a recoverable `Ldc` lane, never
/// a placeholder. 0/1/-1 are the `Special` lanes (no table entry); every OTHER
/// value must be a real entry so `const_idx` maps it to a true index. Returns
/// `true` for the non-special values that therefore belong in the const table.
fn needs_const_entry(c: u32) -> bool {
    c != 0 && c != 1 && c != NEG_ONE_U32
}

/// Push every folded base-field scalar a `LinearComb` column contributes (the
/// column constant + each term coefficient) into `acc`. These are the values
/// `macros::lower_cache` emits as `Ldc(constant)` / `Ldc(coeff)` lanes for the
/// SingleColumnLookup (id 16) and VectorizedLookup (id 17) routines.
fn collect_lincomb_consts(col: &LinearComb, acc: &mut Vec<u32>) {
    if needs_const_entry(col.constant) {
        acc.push(col.constant);
    }
    for &(coeff, _node) in &col.terms {
        if needs_const_entry(coeff) {
            acc.push(coeff);
        }
    }
}

/// Push every folded base-field scalar a MemoryTuple descriptor (id 19) carries:
/// the constant address-space payload, the constant address terms
/// (`Constant`/`ConstantU16`), the `timestamp_offset`, and the special-indirect
/// `low_dynamic_offset` coefficient + `low_offset`. The `perm_additive` seed and
/// the per-role permutation challenges are NOT here — they are CHALLENGES read
/// from the perm/additive bank by role (`bench_interp/tests.rs::indep_mem_tuple`
/// uses `ch.perm_additive` / `ch.perm_challenges[role]`), not base-field
/// constants, so they never ride an `Ldc{Const}` lane.
fn collect_memtup_consts(rel: &cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation, acc: &mut Vec<u32>) {
    if let CompiledAddressSpaceRelationStrict::Constant(c) = &rel.address_space {
        if needs_const_entry(*c) {
            acc.push(*c);
        }
    }
    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            let c = *c as u32;
            if needs_const_entry(c) {
                acc.push(c);
            }
        }
        CompiledAddressStrict::Constant(c) => {
            if needs_const_entry(*c) {
                acc.push(*c);
            }
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect { low_dynamic_offset, low_offset, .. } => {
            if let Some((dyn_coeff, _)) = low_dynamic_offset {
                let dc = *dyn_coeff as u32;
                if needs_const_entry(dc) {
                    acc.push(dc);
                }
            }
            if needs_const_entry(*low_offset) {
                acc.push(*low_offset);
            }
        }
        _ => {}
    }
    if let CompiledMemoryTimestamp::Normal(_) = &rel.timestamp {
        if needs_const_entry(rel.timestamp_offset) {
            acc.push(rel.timestamp_offset);
        }
    }
}

/// R2 const-table augmentation (v2-only; v1 `build_const_table` is untouched).
///
/// v1's table scans the ARENA only, so the cache `LinearComb` coefficients +
/// constants and the MemoryTuple folded constants — which `macros::lower_cache`
/// must now emit as `Ldc{Const}` lanes — were absent and would have mapped to a
/// placeholder. This UNIONS the arena consts with those cache/memtup consts,
/// keeping the v1 dedup + sort + 0/1/-1 exclusion, so `const_idx` resolves every
/// emitted coefficient/constant lane to a real (recoverable) index.
///
/// The returned table is a superset of `build_const_table(arena)` — every arena
/// const keeps an entry — so base-arith `Ldc{Const}` lookups still succeed; only
/// new cache/memtup scalars are added. The `<= 4096` cap is the 12-bit
/// `LDC_IDX_BITS` field (far above the corpus's few hundred entries).
pub(crate) fn build_const_table_v2(layer: &CodegenLayer) -> Vec<u32> {
    let arena: &[ExprNode] = &layer.arena.nodes;
    let mut consts: Vec<u32> = arena
        .iter()
        .filter_map(|n| match n {
            ExprNode::Constant(c) if needs_const_entry(*c) => Some(*c),
            _ => None,
        })
        .collect();
    for cache in &layer.caches {
        match &cache.kind {
            CacheKind::SingleColumnLookup { column, .. } => {
                collect_lincomb_consts(column, &mut consts);
            }
            CacheKind::VectorizedLookup { columns, .. } => {
                for col in columns {
                    collect_lincomb_consts(col, &mut consts);
                    // The self-describing layout (id 17) prefixes each column
                    // group with an `Ldc(term_count)` lane; the count VALUE must
                    // be recoverable, so non-special counts (>= 2) need an entry.
                    let tc = col.terms.len() as u32;
                    if needs_const_entry(tc) {
                        consts.push(tc);
                    }
                }
            }
            CacheKind::MemoryTuple { descriptor } => {
                collect_memtup_consts(&descriptor.descriptor, &mut consts);
            }
            CacheKind::VectorizedLookupSetup => {}
        }
    }
    consts.sort_unstable();
    consts.dedup();
    assert!(consts.len() <= 4096, "v2 const table exceeds 12-bit LDC_IDX_BITS space");
    consts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge_channel_by_family() {
        assert_eq!(bank_for_family(ChallengeFamily::Alpha), LdcSub::ConstChallenge);
        assert_eq!(bank_for_family(ChallengeFamily::Gamma), LdcSub::ConstChallenge);
        assert_eq!(bank_for_family(ChallengeFamily::PermLinearization), LdcSub::ArgChallenge);
        assert_eq!(bank_for_family(ChallengeFamily::AdditiveSeed), LdcSub::ArgChallenge);
    }

    #[test]
    fn alpha_powers_are_column_indexed() {
        // col_0 = α^0 = 1 (multiply-free lift); col_k reads bank entry k.
        assert_eq!(alpha_power_bank_index(0), AlphaSlot::OneLift);
        assert_eq!(alpha_power_bank_index(5), AlphaSlot::Power(5));
    }

    #[test]
    fn v2_const_table_is_superset_and_covers_cache_scalars() {
        // R2: the v2 table must (a) keep every v1 arena const (so base-arith
        // lookups still resolve) and (b) contain every cache/memtup folded scalar
        // a lowering will emit as `Ldc{Const}` (so a coefficient is never a
        // placeholder). Verified corpus-wide and proven non-vacuous.
        use crate::compiler::build_const_table as build_const_table_v1;
        use crate::test_support::all_fixtures;
        use cs::gkr_compiler::CompiledAddressStrict;
        use gkr_design_space::import::load_circuit;
        use std::collections::HashSet;

        let mut saw_cache_scalar = false;
        for p in all_fixtures() {
            let Ok(c) = load_circuit(&p) else { continue };
            for layer in &c.circuit.layers {
                let v1: HashSet<u32> =
                    build_const_table_v1(&layer.arena.nodes).into_iter().collect();
                let v2: HashSet<u32> = build_const_table_v2(layer).into_iter().collect();
                // (a) superset.
                assert!(v1.is_subset(&v2), "v2 const table dropped an arena const");

                // (b) every cache/memtup folded scalar is present (non 0/1/-1).
                let expect = |c: u32, saw: &mut bool| {
                    if needs_const_entry(c) {
                        assert!(v2.contains(&c), "v2 const table missing folded scalar {c}");
                        *saw = true;
                    }
                };
                for cache in &layer.caches {
                    match &cache.kind {
                        CacheKind::SingleColumnLookup { column, .. } => {
                            expect(column.constant, &mut saw_cache_scalar);
                            for &(coeff, _) in &column.terms {
                                expect(coeff, &mut saw_cache_scalar);
                            }
                        }
                        CacheKind::VectorizedLookup { columns, .. } => {
                            for col in columns {
                                expect(col.constant, &mut saw_cache_scalar);
                                expect(col.terms.len() as u32, &mut saw_cache_scalar);
                                for &(coeff, _) in &col.terms {
                                    expect(coeff, &mut saw_cache_scalar);
                                }
                            }
                        }
                        CacheKind::MemoryTuple { descriptor } => {
                            let rel = &descriptor.descriptor;
                            match &rel.address {
                                CompiledAddressStrict::Constant(c) => {
                                    expect(*c, &mut saw_cache_scalar)
                                }
                                CompiledAddressStrict::ConstantU16(c) => {
                                    expect(*c as u32, &mut saw_cache_scalar)
                                }
                                CompiledAddressStrict::U32SpaceSpecialIndirect {
                                    low_dynamic_offset,
                                    low_offset,
                                    ..
                                } => {
                                    expect(*low_offset, &mut saw_cache_scalar);
                                    if let Some((dc, _)) = low_dynamic_offset {
                                        expect(*dc as u32, &mut saw_cache_scalar);
                                    }
                                }
                                _ => {}
                            }
                            if let CompiledMemoryTimestamp::Normal(_) = &rel.timestamp {
                                expect(rel.timestamp_offset, &mut saw_cache_scalar);
                            }
                        }
                        CacheKind::VectorizedLookupSetup => {}
                    }
                }
            }
        }
        assert!(saw_cache_scalar, "no cache/memtup folded scalar in the corpus (test vacuous)");
    }
}
