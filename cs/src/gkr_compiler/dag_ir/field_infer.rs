//! Field-kind inference for the DAG IR.
//!
//! # Rules
//! - `join(Base, Base) = Base`; otherwise `Ext`.
//! - `source_field`: `Constant | LookupValue | VirtualSetup → Base`, `Challenge → Ext`,
//!   `Prior{id}` → the field of the referenced root's `SinkInfo`, `Read{place}` → delegated
//!   to `read_place_field` (see below).
//! - `expr_field`: `Source(s)` → `source_field(s)`; `Add`/`Mul` → `join` over arg fields.
//!
//! # Cross-layer reads (DONE_WITH_CONCERNS)
//! `ReadPlace::LayerOutput` and `ReadPlace::CacheOutput` carry no field tag in the model.
//! The field depends on the *producing* layer's output, which only the generator (Task 7)
//! can supply.  `read_place_field` therefore returns `None` for those two variants;
//! callers that need a definitive answer must supply a resolver or consult the generator.
//! Base-storage places (`BaseLayerMemory`, `BaseLayerWitness`, `Setup`, `Scratch`) always
//! return `Some(Base)`.

use super::{ExprId, Expr, FieldKind, ReadPlace, Root, SinkId, SinkInfo, SourceId, SourceInfo, SourceKind};

// ── join ─────────────────────────────────────────────────────────────────────

/// Lattice join: `Base ⊔ Base = Base`, anything involving `Ext` gives `Ext`.
pub fn join(a: FieldKind, b: FieldKind) -> FieldKind {
    match (a, b) {
        (FieldKind::Base, FieldKind::Base) => FieldKind::Base,
        _ => FieldKind::Ext,
    }
}

// ── read_place_field ──────────────────────────────────────────────────────────

/// Returns the field kind for a `ReadPlace`.
///
/// Returns `Some(Base)` for base-storage places.
/// Returns `None` for `LayerOutput` and `CacheOutput` — those require a cross-layer
/// resolver that only the generator (Task 7) can provide.
pub fn read_place_field(place: &ReadPlace) -> Option<FieldKind> {
    match place {
        ReadPlace::BaseLayerMemory { .. }
        | ReadPlace::BaseLayerWitness { .. }
        | ReadPlace::Setup { .. }
        | ReadPlace::Scratch { .. } => Some(FieldKind::Base),
        ReadPlace::LayerOutput { .. } | ReadPlace::CacheOutput { .. } => None,
    }
}

// ── source_field ──────────────────────────────────────────────────────────────

/// Infers the field kind for a `SourceKind`.
///
/// `roots` and `sinks` are the layer's root and sink tables — needed to resolve
/// `Prior` references.
///
/// Returns `Ok(FieldKind)` for all determinable cases.
/// Returns `Err(ReadPlace)` when the source is `Read{LayerOutput|CacheOutput}` and
/// the field cannot be determined without a cross-layer resolver.
pub fn source_field(
    kind: &SourceKind,
    roots: &[Root],
    sinks: &[SinkInfo],
) -> Result<FieldKind, ReadPlace> {
    match kind {
        SourceKind::Constant { .. } => Ok(FieldKind::Base),
        SourceKind::LookupValue { .. } => Ok(FieldKind::Base),
        SourceKind::VirtualSetup { .. } => Ok(FieldKind::Base),
        SourceKind::Challenge { .. } => Ok(FieldKind::Ext),

        SourceKind::Prior { id } => {
            // A Prior references an Output root; retrieve the sink's declared field.
            let root = &roots[id.0 as usize];
            match root {
                Root::Output { sink, .. } => {
                    let sink_info = &sinks[sink.0 as usize];
                    Ok(sink_info.field)
                }
                Root::Constraint { .. } => unreachable!("Prior must reference an Output root, not a Constraint root"),
            }
        }

        SourceKind::Read { place } => {
            read_place_field(place).ok_or_else(|| place.clone())
        }
    }
}

// ── expr_field ────────────────────────────────────────────────────────────────

/// Infers the field kind for an expression identified by `id`.
///
/// `exprs` is the layer's expression table; `sources` is the layer's source table.
/// `roots` and `sinks` are forwarded to `source_field` for `Prior` resolution.
///
/// Returns `Ok(FieldKind)` when all referenced sources are determinable.
/// Returns the first `Err(ReadPlace)` encountered for cross-layer reads.
pub fn expr_field(
    exprs: &[Expr],
    sources: &[SourceInfo],
    id: ExprId,
    roots: &[Root],
    sinks: &[SinkInfo],
) -> Result<FieldKind, ReadPlace> {
    match &exprs[id.0 as usize] {
        Expr::Source(src_id) => source_field(&sources[src_id.0 as usize].kind, roots, sinks),

        Expr::Add(args) | Expr::Mul(args) => {
            let mut acc = FieldKind::Base;
            for &arg_id in args {
                let f = expr_field(exprs, sources, arg_id, roots, sinks)?;
                acc = join(acc, f);
                // Short-circuit: once Ext, can't go back to Base.
                if acc == FieldKind::Ext {
                    return Ok(FieldKind::Ext);
                }
            }
            Ok(acc)
        }
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::{
        ChallengePower, ChallengeKey, ChallengeRef, ExprId, Expr, FieldKind, LookupValueKind,
        ReadPlace, Root, RootId, SinkId, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
        VirtualSetupKind,
    };

    // ── join ──────────────────────────────────────────────────────────────────

    #[test]
    fn join_base_base_is_base() {
        assert_eq!(join(FieldKind::Base, FieldKind::Base), FieldKind::Base);
    }

    #[test]
    fn join_base_ext_is_ext() {
        assert_eq!(join(FieldKind::Base, FieldKind::Ext), FieldKind::Ext);
    }

    #[test]
    fn join_ext_base_is_ext() {
        assert_eq!(join(FieldKind::Ext, FieldKind::Base), FieldKind::Ext);
    }

    #[test]
    fn join_ext_ext_is_ext() {
        assert_eq!(join(FieldKind::Ext, FieldKind::Ext), FieldKind::Ext);
    }

    // ── source_field: determinable cases ──────────────────────────────────────

    #[test]
    fn source_constant_is_base() {
        let kind = SourceKind::Constant { value: 0 };
        assert_eq!(source_field(&kind, &[], &[]), Ok(FieldKind::Base));
    }

    #[test]
    fn source_lookup_value_is_base() {
        let kind = SourceKind::LookupValue {
            kind: LookupValueKind::RangeCheck16Index,
            set_index: 0,
            query: ExprId(0),
        };
        assert_eq!(source_field(&kind, &[], &[]), Ok(FieldKind::Base));
    }

    #[test]
    fn source_virtual_setup_is_base() {
        let kind = SourceKind::VirtualSetup { kind: VirtualSetupKind::RangeCheck16Bits };
        assert_eq!(source_field(&kind, &[], &[]), Ok(FieldKind::Base));
    }

    #[test]
    fn source_challenge_is_ext() {
        let kind = SourceKind::Challenge {
            reference: ChallengeRef {
                key: ChallengeKey::ConstraintAggregation,
                power: ChallengePower::One,
            },
        };
        assert_eq!(source_field(&kind, &[], &[]), Ok(FieldKind::Ext));
    }

    // ── source_field: base-storage reads return Some(Base) ────────────────────

    #[test]
    fn read_place_base_layer_memory_is_base() {
        assert_eq!(read_place_field(&ReadPlace::BaseLayerMemory { column: 0 }), Some(FieldKind::Base));
    }

    #[test]
    fn read_place_scratch_is_base() {
        assert_eq!(read_place_field(&ReadPlace::Scratch { slot: 0 }), Some(FieldKind::Base));
    }

    #[test]
    fn read_place_base_layer_witness_is_base() {
        assert_eq!(read_place_field(&ReadPlace::BaseLayerWitness { column: 0 }), Some(FieldKind::Base));
    }

    #[test]
    fn read_place_setup_is_base() {
        assert_eq!(read_place_field(&ReadPlace::Setup { column: 0 }), Some(FieldKind::Base));
    }

    // ── source_field: cross-layer reads return Err ────────────────────────────

    #[test]
    fn read_place_layer_output_returns_none() {
        assert_eq!(read_place_field(&ReadPlace::LayerOutput { layer: 0, offset: 0 }), None);
    }

    #[test]
    fn read_place_cache_output_returns_none() {
        assert_eq!(read_place_field(&ReadPlace::CacheOutput { layer: 0, offset: 0 }), None);
    }

    #[test]
    fn source_read_layer_output_returns_err() {
        let place = ReadPlace::LayerOutput { layer: 1, offset: 3 };
        let kind = SourceKind::Read { place: place.clone() };
        assert!(matches!(source_field(&kind, &[], &[]), Err(ReadPlace::LayerOutput { .. })));
    }

    // ── source_field: Prior follows sink field ────────────────────────────────

    #[test]
    fn source_prior_follows_sink_field_base() {
        let sink = SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base };
        let root = Root::Output { expr: ExprId(0), sink: SinkId(0) };
        let kind = SourceKind::Prior { id: RootId(0) };
        assert_eq!(source_field(&kind, &[root], &[sink]), Ok(FieldKind::Base));
    }

    #[test]
    fn source_prior_follows_sink_field_ext() {
        let sink = SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Ext };
        let root = Root::Output { expr: ExprId(0), sink: SinkId(0) };
        let kind = SourceKind::Prior { id: RootId(0) };
        assert_eq!(source_field(&kind, &[root], &[sink]), Ok(FieldKind::Ext));
    }

    // ── expr_field ────────────────────────────────────────────────────────────

    /// Build a small expression table: two sources and a Mul over them.
    /// Mul(Constant, Challenge) → Ext.
    #[test]
    fn expr_field_mul_constant_challenge_is_ext() {
        let sources = vec![
            SourceInfo { kind: SourceKind::Constant { value: 7 } },
            SourceInfo {
                kind: SourceKind::Challenge {
                    reference: ChallengeRef {
                        key: ChallengeKey::ConstraintAggregation,
                        power: ChallengePower::One,
                    },
                },
            },
        ];

        // Expr 0: Source(SourceId(0)) — Constant
        // Expr 1: Source(SourceId(1)) — Challenge
        // Expr 2: Mul([ExprId(0), ExprId(1)])
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
        ];

        let result = expr_field(&exprs, &sources, ExprId(2), &[], &[]);
        assert_eq!(result, Ok(FieldKind::Ext));
    }

    #[test]
    fn expr_field_add_base_base_is_base() {
        let sources = vec![
            SourceInfo { kind: SourceKind::Constant { value: 1 } },
            SourceInfo { kind: SourceKind::LookupValue {
                kind: LookupValueKind::TimestampIndex,
                set_index: 0,
                query: ExprId(0),
            }},
        ];

        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Add(vec![ExprId(0), ExprId(1)]),
        ];

        let result = expr_field(&exprs, &sources, ExprId(2), &[], &[]);
        assert_eq!(result, Ok(FieldKind::Base));
    }

    #[test]
    fn source_field_read_scratch_is_base() {
        let kind = SourceKind::Read { place: ReadPlace::Scratch { slot: 0 } };
        assert_eq!(source_field(&kind, &[], &[]), Ok(FieldKind::Base));
    }
}
