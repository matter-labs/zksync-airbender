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

// NOTE: ExprId/FieldKind/RootId are already imported at the top of schedule.rs (Task 1) — do NOT
// re-import them here or you get E0252 (review #5/F2). Import only the validator-specific items.
use crate::gkr_compiler::dag_ir::{cross_layer_field_map_upto, resolve_expr_field, DagCircuit, DagLayer};
use std::collections::HashSet;

/// Pure structural + width validation of a persisted schedule against its circuit.
/// No extraction/search/scoring logic — that lives test-side in the producer.
pub fn validate_circuit_schedule(circuit: &DagCircuit, sched: &CircuitSchedule) -> Result<(), String> {
    if sched.layers.len() != circuit.layers.len() {
        return Err(format!(
            "schedule has {} layers, circuit has {}",
            sched.layers.len(),
            circuit.layers.len()
        ));
    }
    for (li, (layer, ls)) in circuit.layers.iter().zip(&sched.layers).enumerate() {
        validate_layer_schedule(circuit, layer, li, ls, sched.budget)
            .map_err(|e| format!("layer {li}: {e}"))?;
    }
    Ok(())
}

fn validate_layer_schedule(
    circuit: &DagCircuit,
    layer: &DagLayer,
    li: usize,
    ls: &LayerSchedule,
    budget: usize,
) -> Result<(), String> {
    // a. order is a permutation of exactly the atom-root set.
    let atoms: Vec<RootId> = layer
        .roots
        .iter()
        .enumerate()
        .filter(|(_, r)| r.materialize.is_some() && r.claim.is_some())
        .map(|(i, _)| RootId(i as u32))
        .collect();
    let atom_set: HashSet<RootId> = atoms.iter().copied().collect();
    let order_set: HashSet<RootId> = ls.order.iter().copied().collect();
    if order_set.len() != ls.order.len() {
        return Err("order has duplicate roots".into());
    }
    if order_set != atom_set {
        return Err(format!(
            "order ({} roots) is not the atom-root set ({} roots)",
            ls.order.len(),
            atoms.len()
        ));
    }
    // c. shape.
    if ls.steps.len() != ls.order.len() {
        return Err(format!("steps.len() {} != order.len() {}", ls.steps.len(), ls.order.len()));
    }
    // Cross-layer field map for this layer (accumulated from layers 0..li).
    let cross = cross_layer_field_map_upto(circuit, li);
    let n_exprs = layer.exprs.len() as u32;
    let cell = |e: ExprId| -> Result<usize, String> {
        if e.0 >= n_exprs {
            return Err(format!("ExprId {} out of range ({})", e.0, n_exprs));
        }
        let f = resolve_expr_field(e, layer, &cross)?;
        Ok(field_cells(f))
    };
    for (si, step) in ls.steps.iter().enumerate() {
        // b/d. range + width-budget + dedup on resident_before and resident_after.
        for set in [&step.resident_before, &step.resident_after] {
            let mut seen = HashSet::new();
            let mut width = 0usize;
            for &e in set {
                if !seen.insert(e) {
                    return Err(format!("step {si}: duplicate resident ExprId {}", e.0));
                }
                width += cell(e)?;
            }
            if width > budget {
                return Err(format!("step {si}: resident width {width} > budget {budget}"));
            }
        }
        // f. event integrity: replay events from resident_before -> resident_after.
        let mut resident: HashSet<ExprId> = step.resident_before.iter().copied().collect();
        for ev in &step.events {
            match ev {
                ReplayEvent::Demand { consumer, input_index, value, .. } => {
                    if *input_index == u32::MAX {
                        return Err(format!("step {si}: root-output sentinel in Demand"));
                    }
                    let _ = cell(*consumer)?;
                    let _ = cell(*value)?;
                }
                ReplayEvent::Admit { value } => {
                    let _ = cell(*value)?;
                    resident.insert(*value);
                }
                ReplayEvent::Evict { value } => {
                    let _ = cell(*value)?;
                    resident.remove(value);
                }
            }
        }
        let after: HashSet<ExprId> = step.resident_after.iter().copied().collect();
        if resident != after {
            return Err(format!("step {si}: replaying events from resident_before != resident_after"));
        }
    }
    // e. floor.
    if ls.floor > ls.predicted_traffic {
        return Err(format!("floor {} > predicted_traffic {}", ls.floor, ls.predicted_traffic));
    }
    Ok(())
}

#[cfg(test)]
mod validator_tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::*;
    use std::collections::BTreeMap;

    // A 1-layer circuit: one atom root (Output+claim) over an Ext add, plus one Base source.
    // exprs: [Source(0)=Base read, Source(1)=Base read, Add([0,1])=Base]; root.expr = ExprId(2).
    fn demo_circuit() -> DagCircuit {
        let layer = DagLayer {
            sources: vec![
                SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 0 } } },
                SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 1 } } },
            ],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1)), Expr::Add(vec![ExprId(0), ExprId(1)])],
            roots: vec![Root {
                expr: ExprId(2),
                materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
                claim: Some(ClaimInfo { origin: RootOrigin {
                    group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(0),
                } }),
            }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        DagCircuit { layers: vec![layer], globals: DagGlobals::default() }
    }

    fn ok_schedule() -> CircuitSchedule {
        CircuitSchedule {
            circuit: "demo".into(),
            budget: 16,
            layers: vec![LayerSchedule {
                order: vec![RootId(0)],
                steps: vec![StepPlan {
                    resident_before: vec![],
                    events: vec![ReplayEvent::Admit { value: ExprId(0) }],
                    resident_after: vec![ExprId(0)],
                }],
                predicted_traffic: 1,
                floor: 1,
            }],
        }
    }

    #[test]
    fn accepts_valid_schedule() {
        assert!(validate_circuit_schedule(&demo_circuit(), &ok_schedule()).is_ok());
    }

    #[test]
    fn rejects_layer_count_mismatch() {
        let mut s = ok_schedule();
        s.layers.push(LayerSchedule { order: vec![], steps: vec![], predicted_traffic: 0, floor: 0 });
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
    }

    #[test]
    fn rejects_out_of_range_root() {
        // RootId(1) does not exist (demo_circuit has 1 root) — covers the range case.
        let mut s = ok_schedule();
        s.layers[0].order = vec![RootId(1)];
        s.layers[0].steps = vec![StepPlan { resident_before: vec![], events: vec![], resident_after: vec![] }];
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
    }

    #[test]
    fn rejects_non_atom_root_in_order() {
        // An IN-RANGE root that is not an atom (claim: None) must be rejected — isolates the
        // atom-set check from the out-of-range case above.
        let mut c = demo_circuit();
        c.layers[0].roots.push(Root {
            expr: ExprId(2),
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 1 }, field: FieldKind::Base }),
            claim: None,
        });
        let mut s = ok_schedule();
        s.layers[0].order = vec![RootId(1)]; // in range now (2 roots), but not an atom root
        s.layers[0].steps = vec![StepPlan { resident_before: vec![], events: vec![], resident_after: vec![] }];
        assert!(validate_circuit_schedule(&c, &s).is_err());
    }

    #[test]
    fn rejects_steps_len_mismatch() {
        let mut s = ok_schedule();
        s.layers[0].steps = vec![];
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
    }

    #[test]
    fn rejects_event_integrity_violation() {
        // resident_before empty + no events should yield empty resident_after; claim [ExprId(0)].
        let mut s = ok_schedule();
        s.layers[0].steps = vec![StepPlan {
            resident_before: vec![],
            events: vec![],
            resident_after: vec![ExprId(0)],
        }];
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
    }

    #[test]
    fn rejects_width_over_budget() {
        // resident_after holds 5 distinct Base values, budget 4 -> 5 cells > 4.
        let mut s = ok_schedule();
        s.budget = 4;
        let vals: Vec<ExprId> = (0..5).map(ExprId).collect();
        // Add 4 sources+exprs so ExprIds 0..5 are in range and Base.
        let mut c = demo_circuit();
        for col in 2..6u32 {
            c.layers[0].sources.push(SourceInfo {
                kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: col as usize } },
            });
            let src_idx = c.layers[0].sources.len() as u32 - 1;
            c.layers[0].exprs.push(Expr::Source(SourceId(src_idx)));
        }
        s.layers[0].steps = vec![StepPlan {
            resident_before: vec![],
            events: vals.iter().map(|&v| ReplayEvent::Admit { value: v }).collect(),
            resident_after: vals,
        }];
        assert!(validate_circuit_schedule(&c, &s).is_err());
    }

    #[test]
    fn rejects_ext_width_over_budget_under_count() {
        // ONE Ext value (4 cells) with budget 3: count (1) is UNDER budget but width (4) is OVER.
        // A count-based regression would wrongly accept this; the width-aware validator rejects it.
        let mut c = demo_circuit();
        // Challenge source -> Ext; Expr::Source referencing it is ExprId(3), resolves to Ext.
        c.layers[0].sources.push(SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::ConstraintAggregation,
                    power: ChallengePower::One,
                },
            },
        });
        let challenge_src = SourceId(c.layers[0].sources.len() as u32 - 1);
        c.layers[0].exprs.push(Expr::Source(challenge_src));
        let ext_val = ExprId(3);

        let mut s = ok_schedule();
        s.budget = 3; // 1 Ext value = 4 cells > 3, while the entry count (1) is <= 3
        s.layers[0].steps = vec![StepPlan {
            resident_before: vec![],
            events: vec![ReplayEvent::Admit { value: ext_val }],
            resident_after: vec![ext_val],
        }];
        assert!(validate_circuit_schedule(&c, &s).is_err());
    }

    #[test]
    fn rejects_floor_above_traffic() {
        let mut s = ok_schedule();
        s.layers[0].floor = 100;
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
    }

    #[test]
    fn rejects_root_output_sentinel_in_demand() {
        let mut s = ok_schedule();
        s.layers[0].steps = vec![StepPlan {
            resident_before: vec![],
            events: vec![ReplayEvent::Demand {
                consumer: ExprId(2), input_index: u32::MAX, value: ExprId(0), kind: DemandKind::Reload,
            }],
            resident_after: vec![],
        }];
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
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
