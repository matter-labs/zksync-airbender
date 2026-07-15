//! `HashResolvers`: the shared, production-grade `Resolvers` implementation
//! for M1's value-parity gate (`tests/m1_parity.rs`).
//!
//! # Determinism by construction
//!
//! Every resolver method here is a pure function of `(self.seed, a fixed
//! per-method tag, the method's structured key, row)`, mixed through a
//! splitmix64-style avalanche (see [`splitmix64`]). There is no shared
//! mutable state and no dependence on call order or call count, so the SAME
//! `HashResolvers { seed }` produces byte-identical values whether it drives
//! `gkr_flatten::ir::interpret` (the flattened `LinearIR`) or
//! `cs::gkr_compiler::dag_ir::eval::eval_layer_root` (the reference
//! DAG-walking evaluator) — which is exactly the property the M1 gate needs:
//! any observed difference between the two evaluators' outputs must come
//! from the walker/interpreter, never from the resolver.
//!
//! Read/Challenge values are hashed into all four `Ext` base-field
//! coefficients independently (not lifted from a single `Bf` draw), so the
//! parity check actually exercises full Ext-width arithmetic rather than the
//! degenerate embedded-base-field subring.
//!
//! # `LookupValue` is query-blind — LOAD-BEARING
//!
//! `gkr_flatten::ir::interpret`'s `LookupValue` leaf never evaluates the
//! lookup's query sub-expression: it passes `Ext::ZERO` in its place (a
//! documented v1 simplification — see `ir.rs`'s module doc). The reference
//! evaluator (`eval_layer_root`) has no such shortcut: it evaluates the real
//! query sub-expression and passes its actual value to
//! `LookupResolver::lookup`. For the two evaluators to agree on every
//! `LookupValue` leaf, [`HashResolvers`]'s `lookup()` MUST ignore
//! `evaluated_query` entirely — it hashes only `(kind, set_index, row)`. A
//! resolver that branched on `evaluated_query` would silently diverge
//! between the flattened and reference paths (zero vs. the real query value)
//! and must never be paired with `ir::interpret` for a parity check.

use std::hash::{Hash, Hasher};

use cs::gkr_compiler::dag_ir::eval::{
    Bf, ChallengeResolver, Ext, LookupResolver, ReadResolver, Resolvers, VirtualSetupResolver,
};
use cs::gkr_compiler::dag_ir::{ChallengeRef, LookupValueKind, ReadPlace, VirtualSetupKind};
use field::{Field, FieldExtension, PrimeField};

/// The splitmix64 output function (Steele/Lea/Flood): a strong avalanche
/// over a 64-bit state, used both as this module's byte-folding [`Hasher`]
/// core and to draw successive independent field-coefficient samples from a
/// single digest.
#[inline]
fn splitmix64(x: u64) -> u64 {
    let mut z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A [`Hasher`] whose state is folded via [`splitmix64`], one input byte at
/// a time. Deterministic across runs/processes for a fixed `seed` (unlike
/// `std::collections::hash_map::DefaultHasher`, whose exact algorithm is not
/// a stability guarantee) — required so `HashResolvers` gives byte-identical
/// answers on both evaluation paths within (and across) a test run.
struct SplitMix64Hasher(u64);

impl Hasher for SplitMix64Hasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = splitmix64(self.0 ^ b as u64);
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

/// Digests `(seed, tag, key, row)` into one `u64`. `tag` disambiguates the
/// four resolver methods (so e.g. a `Read` and a `Challenge` whose structured
/// keys happen to hash identically still diverge); `key` is any
/// `Hash`-deriving structured payload (a `ReadPlace`, `ChallengeRef`, ...).
fn digest<T: Hash + ?Sized>(seed: u64, tag: u64, key: &T, row: usize) -> u64 {
    let mut h = SplitMix64Hasher(seed);
    tag.hash(&mut h);
    key.hash(&mut h);
    row.hash(&mut h);
    h.finish()
}

/// Hashes `(seed, tag, key, row)` down to one `Bf` element.
fn hash_bf<T: Hash + ?Sized>(seed: u64, tag: u64, key: &T, row: usize) -> Bf {
    let d = digest(seed, tag, key, row);
    Bf::from_u32_with_reduction((d & 0xFFFF_FFFF) as u32)
}

/// Hashes `(seed, tag, key, row)` down to a full `Ext` element: four
/// independent `Bf` coefficients drawn from successive `splitmix64` outputs
/// seeded by the digest, so the result exercises all four Ext dimensions
/// rather than a base-field-embedded value.
fn hash_ext<T: Hash + ?Sized>(seed: u64, tag: u64, key: &T, row: usize) -> Ext {
    let mut state = digest(seed, tag, key, row);
    let mut coeffs = [Bf::ZERO; 4];
    for c in coeffs.iter_mut() {
        state = splitmix64(state);
        *c = Bf::from_u32_with_reduction((state & 0xFFFF_FFFF) as u32);
    }
    <Ext as FieldExtension<Bf>>::from_coeffs(coeffs)
}

// Per-method tags: distinguish the four resolver methods so structurally
// identical keys hashed by different methods never collide.
const TAG_READ: u64 = 1;
const TAG_LOOKUP: u64 = 2;
const TAG_VIRTUAL_SETUP: u64 = 3;
const TAG_CHALLENGE: u64 = 4;

/// Deterministic, seeded, splitmix64-style implementation of every
/// `dag_ir::eval` resolver trait — the shared production resolver for M1's
/// parity gate (see module docs for the determinism argument and the
/// `LookupValue` query-blindness requirement).
#[derive(Debug, Clone, Copy)]
pub struct HashResolvers {
    pub seed: u64,
}

impl HashResolvers {
    /// Bundles `self` into a `Resolvers<'_>` (all four trait objects borrow
    /// the same `HashResolvers`).
    pub fn bundle(&self) -> Resolvers<'_> {
        Resolvers { read: self, lookup: self, virtual_setup: self, challenge: self }
    }
}

impl ReadResolver for HashResolvers {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        hash_ext(self.seed, TAG_READ, place, row)
    }
}

impl LookupResolver for HashResolvers {
    /// IGNORES `evaluated_query` — see this module's doc for why that is
    /// required, not incidental.
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        _evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        hash_bf(self.seed, TAG_LOOKUP, &(kind, set_index), row)
    }
}

impl VirtualSetupResolver for HashResolvers {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        hash_bf(self.seed, TAG_VIRTUAL_SETUP, kind, row)
    }
}

impl ChallengeResolver for HashResolvers {
    fn challenge(&self, reference: &ChallengeRef) -> Ext {
        // Challenges carry no row: identical across every row of a layer.
        hash_ext(self.seed, TAG_CHALLENGE, reference, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_across_calls() {
        let a = HashResolvers { seed: 7 };
        let b = HashResolvers { seed: 7 };
        let place = ReadPlace::BaseLayerWitness { column: 3 };
        assert_eq!(a.read(&place, 5), b.read(&place, 5));
        assert_eq!(a.read(&place, 5), a.read(&place, 5), "same call twice, same answer");
    }

    #[test]
    fn different_seeds_diverge() {
        let a = HashResolvers { seed: 1 };
        let b = HashResolvers { seed: 2 };
        let place = ReadPlace::BaseLayerWitness { column: 3 };
        assert_ne!(a.read(&place, 5), b.read(&place, 5));
    }

    #[test]
    fn lookup_ignores_evaluated_query() {
        let r = HashResolvers { seed: 42 };
        let kind = LookupValueKind::GenericColumn { column: 1 };
        let q0 = LookupResolver::lookup(&r, &kind, 3, Ext::ZERO, 9);
        let q1 = LookupResolver::lookup(&r, &kind, 3, hash_ext(1, 1, &0u8, 0), 9);
        assert_eq!(q0, q1, "lookup() must be blind to evaluated_query");
    }

    #[test]
    fn distinct_read_places_diverge() {
        let r = HashResolvers { seed: 7 };
        let a = r.read(&ReadPlace::BaseLayerWitness { column: 0 }, 0);
        let b = r.read(&ReadPlace::BaseLayerMemory { column: 0 }, 0);
        assert_ne!(a, b, "distinct ReadPlace variants must not collide");
    }

    #[test]
    fn ext_uses_all_four_coefficients() {
        // Regression guard against accidentally lifting a single Bf draw
        // into Ext (which would leave c1 == Ext::ZERO's upper half).
        let r = HashResolvers { seed: 7 };
        let v = r.read(&ReadPlace::Scratch { slot: 11 }, 4);
        let coeffs = <Ext as FieldExtension<Bf>>::into_coeffs(v);
        assert!(coeffs.iter().any(|c| *c != Bf::ZERO), "at least one nonzero coeff");
        // Not all four independently-drawn coefficients collapse to the same
        // value (would indicate the per-coefficient loop isn't advancing).
        assert!(
            coeffs[0] != coeffs[1] || coeffs[1] != coeffs[2] || coeffs[2] != coeffs[3],
            "coefficients should not be degenerate: {coeffs:?}"
        );
    }
}
