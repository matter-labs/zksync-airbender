//! Expression-level resolution lowering (spec §9): prune resolved fold subtrees to one Special.

use super::super::source::{lower_resolution, SpecialTable};
use cs::gkr_compiler::dag_ir::{DagLayer, ExprId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolveOutcome {
    Special(u16),
    Descend,
}

/// If `expr_id` carries a ResolutionStrategy, emit one Special (carrying origin_expr) and prune.
pub fn resolve_or_descend(
    layer: &DagLayer,
    expr_id: ExprId,
    specials: &mut SpecialTable,
) -> ResolveOutcome {
    match layer.resolutions.get(&expr_id) {
        Some(strategy) => {
            ResolveOutcome::Special(specials.push(lower_resolution(strategy, expr_id)))
        }
        None => ResolveOutcome::Descend,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ClaimInfo, DagLayer, FieldKind, ResolutionStrategy, Root,
        RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceKind,
    };
    use std::collections::BTreeMap;

    #[test]
    fn resolved_expr_emits_one_special_and_prunes() {
        // build a layer where ExprId(of a fold) carries PeekSetup
        let mut arena = ArenaBuilder::new();
        let s0 = arena.intern_source(SourceKind::Constant { value: 0 });
        let e = arena.source_expr(s0);
        let s1 = arena.intern_source(SourceKind::Constant { value: 1 });
        let other = arena.source_expr(s1); // a second expr NOT carrying a resolution
        let mut resolutions = BTreeMap::new();
        resolutions.insert(e, ResolutionStrategy::PeekSetup);
        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![Root {
                expr: e,
                materialize: Some(SinkInfo {
                    kind: SinkKind::Inner { layer: 0, offset: 0 },
                    field: FieldKind::Base,
                }),
                claim: Some(ClaimInfo {
                    origin: RootOrigin {
                        group: RootGroup::Gates,
                        relation_index: 0,
                        slot: RootSlot::Output(0),
                    },
                }),
            }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions,
        };
        let mut specials = SpecialTable::default();
        assert!(matches!(resolve_or_descend(&layer, e, &mut specials), ResolveOutcome::Special(0)));
        assert_eq!(specials.len(), 1);
        assert_eq!(specials.get(0).unwrap().origin_expr, e);
        // an unresolved expr descends (and emits no new special)
        assert_eq!(resolve_or_descend(&layer, other, &mut specials), ResolveOutcome::Descend);
        assert_eq!(specials.len(), 1);
    }
}
