//! Field-kind inference for the DAG IR.
//!
//!
//! Cross-layer reads require the producing layer's field from a resolver.

use super::{Expr, ExprId, FieldKind, ReadPlace, SourceKind};

/// Lattice join: `Base ⊔ Base = Base`, anything involving `Ext` gives `Ext`.
pub(crate) fn join(a: FieldKind, b: FieldKind) -> FieldKind {
    match (a, b) {
        (FieldKind::Base, FieldKind::Base) => FieldKind::Base,
        _ => FieldKind::Ext,
    }
}

/// Returns `None` for cross-layer reads, which require a resolver.
pub fn read_place_field(place: &ReadPlace) -> Option<FieldKind> {
    match place {
        ReadPlace::BaseLayerMemory { .. }
        | ReadPlace::BaseLayerWitness { .. }
        | ReadPlace::Setup { .. }
        | ReadPlace::Scratch { .. } => Some(FieldKind::Base),
        ReadPlace::LayerOutput { .. } | ReadPlace::CacheOutput { .. } => None,
    }
}

pub(crate) fn source_field(kind: &SourceKind) -> Result<FieldKind, ReadPlace> {
    match kind {
        SourceKind::Constant { .. } | SourceKind::InitsAndTeardownsTopBits { .. } => {
            Ok(FieldKind::Base)
        }
        SourceKind::LookupValue { .. } => Ok(FieldKind::Base),
        SourceKind::VirtualSetup { .. } => Ok(FieldKind::Base),
        SourceKind::Challenge { .. } => Ok(FieldKind::Ext),

        SourceKind::Read { place } => read_place_field(place).ok_or(*place),
    }
}

/// Infer an expression field, using `resolve` for cross-layer reads.
pub fn expr_field_with_resolver(
    exprs: &[Expr],
    sources: &[SourceKind],
    id: ExprId,
    resolve: &impl Fn(&ReadPlace) -> Option<FieldKind>,
) -> Result<FieldKind, ReadPlace> {
    match &exprs[id.0 as usize] {
        Expr::Source(src_id) => match source_field(&sources[src_id.0 as usize]) {
            Ok(field) => Ok(field),
            Err(place) => resolve(&place).ok_or(place),
        },

        Expr::Add(args) | Expr::Mul(args) => {
            let mut acc = FieldKind::Base;
            for &arg_id in args {
                let f = expr_field_with_resolver(exprs, sources, arg_id, resolve)?;
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
    use crate::{
        ChallengeKey, ChallengePower, ChallengeRef, Expr, ExprId, FieldKind, LookupValueKind,
        ReadPlace, SourceId, SourceKind, VirtualSetupKind,
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
        assert_eq!(source_field(&kind), Ok(FieldKind::Base));
    }

    #[test]
    fn source_lookup_value_is_base() {
        let kind = SourceKind::LookupValue {
            kind: LookupValueKind::RangeCheck16Index,
            set_index: 0,
            query: ExprId(0),
        };
        assert_eq!(source_field(&kind), Ok(FieldKind::Base));
    }

    #[test]
    fn source_virtual_setup_is_base() {
        let kind = SourceKind::VirtualSetup {
            kind: VirtualSetupKind::RangeCheck16Bits,
        };
        assert_eq!(source_field(&kind), Ok(FieldKind::Base));
    }

    #[test]
    fn source_challenge_is_ext() {
        let kind = SourceKind::Challenge {
            reference: ChallengeRef {
                key: ChallengeKey::ClaimBatching,
                power: ChallengePower::One,
            },
        };
        assert_eq!(source_field(&kind), Ok(FieldKind::Ext));
    }

    // ── source_field: base-storage reads return Some(Base) ────────────────────

    #[test]
    fn read_place_base_layer_memory_is_base() {
        assert_eq!(
            read_place_field(&ReadPlace::BaseLayerMemory { column: 0 }),
            Some(FieldKind::Base)
        );
    }

    #[test]
    fn read_place_scratch_is_base() {
        assert_eq!(
            read_place_field(&ReadPlace::Scratch { slot: 0 }),
            Some(FieldKind::Base)
        );
    }

    #[test]
    fn read_place_base_layer_witness_is_base() {
        assert_eq!(
            read_place_field(&ReadPlace::BaseLayerWitness { column: 0 }),
            Some(FieldKind::Base)
        );
    }

    #[test]
    fn read_place_setup_is_base() {
        assert_eq!(
            read_place_field(&ReadPlace::Setup { column: 0 }),
            Some(FieldKind::Base)
        );
    }

    // ── source_field: cross-layer reads return Err ────────────────────────────

    #[test]
    fn read_place_layer_output_returns_none() {
        assert_eq!(
            read_place_field(&ReadPlace::LayerOutput {
                layer: 0,
                offset: 0
            }),
            None
        );
    }

    #[test]
    fn read_place_cache_output_returns_none() {
        assert_eq!(
            read_place_field(&ReadPlace::CacheOutput {
                layer: 0,
                offset: 0
            }),
            None
        );
    }

    #[test]
    fn source_read_layer_output_returns_err() {
        let place = ReadPlace::LayerOutput {
            layer: 1,
            offset: 3,
        };
        let kind = SourceKind::Read { place };
        assert!(matches!(
            source_field(&kind),
            Err(ReadPlace::LayerOutput { .. })
        ));
    }

    #[test]
    fn expr_field_mul_constant_challenge_is_ext() {
        let sources = vec![
            SourceKind::Constant { value: 7 },
            SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::ClaimBatching,
                    power: ChallengePower::One,
                },
            },
        ];

        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
        ];

        let result = expr_field_with_resolver(&exprs, &sources, ExprId(2), &|_| None);
        assert_eq!(result, Ok(FieldKind::Ext));
    }

    #[test]
    fn expr_field_add_base_base_is_base() {
        let sources = vec![
            SourceKind::Constant { value: 1 },
            SourceKind::LookupValue {
                kind: LookupValueKind::TimestampIndex,
                set_index: 0,
                query: ExprId(0),
            },
        ];

        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Add(vec![ExprId(0), ExprId(1)]),
        ];

        let result = expr_field_with_resolver(&exprs, &sources, ExprId(2), &|_| None);
        assert_eq!(result, Ok(FieldKind::Base));
    }

    #[test]
    fn source_field_read_scratch_is_base() {
        let kind = SourceKind::Read {
            place: ReadPlace::Scratch { slot: 0 },
        };
        assert_eq!(source_field(&kind), Ok(FieldKind::Base));
    }
}
