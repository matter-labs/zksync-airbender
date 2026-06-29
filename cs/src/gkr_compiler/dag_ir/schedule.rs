//! Persisted, decoded schedule for the forward pass (GKR Stage 2b).
//!
//! Produced on-demand by the metaheuristic optimizer (test-tier in `gkr_eval_isa`),
//! consumed by Stage 3's forward-program generator. Self-contained: the ordered
//! `ReplayEvent` stream captures the searched order AND eviction/recovery policy.
//! Slot-free — residency is value-set membership; Stage 3 allocates cells deterministically.

use crate::gkr_compiler::dag_ir::{ExprId, FieldKind, RootId};

/// One scheduled circuit at one budget. `layers` is index-aligned with `DagCircuit.layers`.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CircuitSchedule {
    pub circuit: String,
    /// Cache budget in CELLS (not entry count). The optimizer input, recorded.
    pub budget: usize,
    pub layers: Vec<LayerSchedule>,
}

/// Schedule for one layer. Empty (`order: []`) when the layer has no atom roots.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LayerSchedule {
    /// Atom roots (`materialize.is_some() && claim.is_some()`) in execution order;
    /// a permutation of exactly this layer's atom-root set.
    pub order: Vec<RootId>,
    /// One plan per `order` entry (same index).
    pub steps: Vec<StepPlan>,
    /// The optimizer's achieved DRAM read traffic (validation/provenance).
    pub predicted_traffic: u64,
    /// `dag_traffic_floor` for this layer (lower bound; validation).
    pub floor: u64,
}

/// The ordered cache actions for one scheduled root. Replaying `events` from
/// `resident_before` reproduces `resident_after` exactly (validator check §5.4f).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct StepPlan {
    /// Resident values entering this root, AFTER cone-fit eviction, BEFORE compute. Membership only.
    pub resident_before: Vec<ExprId>,
    /// Ordered intra-root replay actions.
    pub events: Vec<ReplayEvent>,
    /// Resident values after finish_root. Validation anchor.
    pub resident_after: Vec<ExprId>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ReplayEvent {
    /// An operand demand resolved as Resident / Reload / Recompute. NOT emitted for the
    /// root-output pseudo-site (the produced value is `layer.roots[order[p]].expr`).
    Demand { consumer: ExprId, input_index: u32, value: ExprId, kind: DemandKind },
    /// A value admitted to cache (incl. a root output admitted as `value = root_expr`).
    Admit { value: ExprId },
    /// Any membership-changing eviction after `resident_before` (dead-resident or pressure victim).
    Evict { value: ExprId },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DemandKind { Resident, Reload, Recompute }

/// Cell width of a value by field: Ext = 4 (BabyBearExt4 degree), Base = 1.
pub fn field_cells(field: FieldKind) -> usize {
    match field {
        FieldKind::Base => 1,
        FieldKind::Ext => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::{ExprId, RootId};

    #[test]
    fn circuit_schedule_serde_roundtrip() {
        let sched = CircuitSchedule {
            circuit: "demo".to_string(),
            budget: 16,
            layers: vec![
                LayerSchedule {
                    order: vec![RootId(0), RootId(2)],
                    steps: vec![
                        StepPlan {
                            resident_before: vec![],
                            events: vec![ReplayEvent::Demand {
                                consumer: ExprId(5),
                                input_index: 1,
                                value: ExprId(3),
                                kind: DemandKind::Reload,
                            }],
                            resident_after: vec![ExprId(3)],
                        },
                        StepPlan {
                            resident_before: vec![ExprId(3)],
                            events: vec![
                                ReplayEvent::Evict { value: ExprId(3) },
                                ReplayEvent::Admit { value: ExprId(7) },
                            ],
                            resident_after: vec![ExprId(7)],
                        },
                    ],
                    predicted_traffic: 12,
                    floor: 9,
                },
                LayerSchedule { order: vec![], steps: vec![], predicted_traffic: 0, floor: 0 },
            ],
        };
        let json = serde_json::to_string(&sched).expect("serialize");
        let back: CircuitSchedule = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, sched);
    }

    #[test]
    fn field_cells_widths() {
        assert_eq!(field_cells(FieldKind::Base), 1);
        assert_eq!(field_cells(FieldKind::Ext), 4);
    }
}
