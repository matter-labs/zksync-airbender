//! Closed symbolic adapter for normalized backward fragments.

use cs::gkr_compiler::dag_ir::{BwdRegime, Expr, ExprId, FieldKind, expr_field, join};

use crate::bwd::compile::{BwdCompiledLayer, fragment_descs, tally_bwd_program};
use crate::bwd::distill::DistilledLayer;
use crate::bwd::source::BwdSpecialTable;
use crate::bwd::trace::{
    BwdCompileTrace, BwdEvent, certify, live_profile, physical_traffic_events, plan_epoch_fragment,
};

use super::{
    ConcreteBindError, ConcreteEvalProgram, ConcreteTerminal, EvalPlan, PackConfig, PackError,
    PackedEvalPlan, PlanError, concrete::bind_backward_packed_plan,
    elaborate_backward_fragments_driver, pack_plan,
};

/// Symbolic backward evaluation before descriptor binding. The special table is
/// cloned and extended only with descriptors actually emitted by the fragment
/// plan, leaving the distilled layer's binding namespace unchanged.
#[derive(Clone, Debug)]
pub struct BackwardSymbolicEvaluation {
    pub plan: EvalPlan,
    pub packed: PackedEvalPlan,
    pub specials: BwdSpecialTable,
    pub(crate) demand_events: Vec<BwdEvent>,
}

pub struct CompiledBackwardEvaluation {
    pub symbolic: BackwardSymbolicEvaluation,
    pub compiled: BwdCompiledLayer,
    pub encoded: Vec<u16>,
    pub trace: BwdCompileTrace,
}

#[derive(Clone, Debug, PartialEq)]
pub enum BackwardEvaluationError {
    Plan(PlanError),
    Pack(PackError),
    BudgetCellsOverflow {
        budget_cells: usize,
    },
    InvalidFragmentOrder {
        order: Vec<usize>,
        fragment_count: usize,
    },
    EmptyFragmentDecomposition,
    Concrete(ConcreteBindError),
    UnboundBackwardSource(ExprId),
    BackwardCommit,
    UnexpectedTerminal,
    ForwardDescriptorLeak,
    TrafficSourceMapping,
    TrafficCertificateMismatch {
        symbolic: usize,
        packed: usize,
        concrete: usize,
        traced: usize,
    },
}

impl From<PlanError> for BackwardEvaluationError {
    fn from(value: PlanError) -> Self {
        Self::Plan(value)
    }
}

impl From<PackError> for BackwardEvaluationError {
    fn from(value: PackError) -> Self {
        Self::Pack(value)
    }
}

/// Elaborate the complete normalized backward-fragment expression without
/// cache residency, then pack it. `budget_cells` is converted exactly once to
/// extension-field lane units before it reaches the shared elaborator.
pub fn elaborate_backward_fragments_uncached(
    d: &DistilledLayer,
    order: Option<&[usize]>,
    budget_cells: usize,
    stream_reductions: bool,
) -> Result<BackwardSymbolicEvaluation, BackwardEvaluationError> {
    let fragments = &d.fragments.fragments;
    if d.fragments.c_init.terms.is_empty() && fragments.is_empty() {
        return Err(BackwardEvaluationError::EmptyFragmentDecomposition);
    }
    let scheduled_fragments = validate_fragment_order(order, fragments.len())?;
    let budget_lanes = budget_cells
        .checked_mul(4)
        .ok_or(BackwardEvaluationError::BudgetCellsOverflow { budget_cells })?;
    let (specials, coefficient_descs, acc_init_desc) = fragment_descs(d);
    let expr_fields = backward_expr_fields(d);
    let (plan, demand_events) = elaborate_backward_fragments_driver(
        &d.layer,
        d.root,
        &expr_fields,
        fragments,
        &scheduled_fragments,
        &coefficient_descs,
        acc_init_desc,
        budget_lanes,
        stream_reductions,
    )?;
    let packed = pack_plan(&plan, &d.layer, PackConfig::default())?;
    Ok(BackwardSymbolicEvaluation {
        plan,
        packed,
        specials,
        demand_events,
    })
}

/// Compile the full backward fragment decomposition through the shared packed
/// evaluation pipeline. The selected reduction mode is explicit and this
/// entry never retries with a different mode.
pub fn compile_backward_fragments_uncached(
    d: &DistilledLayer,
    order: Option<&[usize]>,
    budget_cells: usize,
    stream_reductions: bool,
) -> Result<CompiledBackwardEvaluation, BackwardEvaluationError> {
    let symbolic =
        elaborate_backward_fragments_uncached(d, order, budget_cells, stream_reductions)?;
    let budget_lanes = symbolic.plan.budget_lanes;
    let bound = bind_backward_packed_plan(
        &symbolic.packed,
        &d.layer,
        d.root,
        budget_lanes,
        &d.leaf_descs,
    )
    .map_err(map_concrete_error)?;
    let ConcreteEvalProgram {
        compiled: forward,
        encoded,
        terminal,
        ..
    } = bound;
    if !matches!(terminal, ConcreteTerminal::ReturnAcc { .. }) {
        return Err(BackwardEvaluationError::UnexpectedTerminal);
    }
    if forward.ctx.specials.len() != 0 {
        return Err(BackwardEvaluationError::ForwardDescriptorLeak);
    }

    let program = forward.program;
    let specials = symbolic.specials.clone();
    let live = live_profile(&program);
    let max_live_lanes = live.iter().copied().max().unwrap_or(0);
    let (mut stats, stats_ext) = tally_bwd_program(&program, &specials);
    stats.max_live_cells = max_live_lanes;
    let compiled = BwdCompiledLayer {
        program,
        specials,
        backings: forward.ctx.backings,
        consts: forward.ctx.consts,
        challenges: forward.ctx.challenges,
        budget: budget_lanes,
        stats,
        stats_ext,
    };

    let mut events = symbolic.demand_events.clone();
    events.extend(
        physical_traffic_events(
            &d.layer,
            &compiled.program,
            &compiled.specials,
            &d.leaf_descs,
            &compiled.backings,
        )
        .ok_or(BackwardEvaluationError::TrafficSourceMapping)?,
    );
    let trace = BwdCompileTrace {
        epoch: plan_epoch_fragment(d, budget_lanes, stream_reductions),
        budget: budget_lanes,
        stream_reductions,
        events,
        free: live
            .into_iter()
            .map(|occupied| budget_lanes.saturating_sub(occupied))
            .collect(),
    };

    let symbolic_traffic = symbolic.plan.stats.dram_read_lanes;
    let packed_traffic = symbolic.packed.stats.dram_read_lanes;
    let concrete_traffic = compiled.stats_ext.global + compiled.stats_ext.fold_traffic;
    let traced_traffic = trace
        .events
        .iter()
        .filter_map(|event| match event {
            BwdEvent::TrafficRead { cells, .. } => Some(*cells as usize),
            _ => None,
        })
        .sum();
    if symbolic_traffic != packed_traffic
        || packed_traffic != concrete_traffic
        || concrete_traffic != traced_traffic
    {
        return Err(BackwardEvaluationError::TrafficCertificateMismatch {
            symbolic: symbolic_traffic,
            packed: packed_traffic,
            concrete: concrete_traffic,
            traced: traced_traffic,
        });
    }
    if d.regime == BwdRegime::Ext && certify(&compiled, &trace).is_err() {
        return Err(BackwardEvaluationError::TrafficCertificateMismatch {
            symbolic: symbolic_traffic,
            packed: packed_traffic,
            concrete: concrete_traffic,
            traced: traced_traffic,
        });
    }

    Ok(CompiledBackwardEvaluation {
        symbolic,
        compiled,
        encoded,
        trace,
    })
}

fn map_concrete_error(error: ConcreteBindError) -> BackwardEvaluationError {
    match error {
        ConcreteBindError::UnboundBackwardSource(expr) => {
            BackwardEvaluationError::UnboundBackwardSource(expr)
        }
        ConcreteBindError::BackwardCommit => BackwardEvaluationError::BackwardCommit,
        other => BackwardEvaluationError::Concrete(other),
    }
}

fn validate_fragment_order(
    order: Option<&[usize]>,
    fragment_count: usize,
) -> Result<Vec<usize>, BackwardEvaluationError> {
    let Some(order) = order else {
        return Ok((0..fragment_count).collect());
    };
    let mut sorted = order.to_vec();
    sorted.sort_unstable();
    if order.len() != fragment_count || sorted != (0..fragment_count).collect::<Vec<_>>() {
        return Err(BackwardEvaluationError::InvalidFragmentOrder {
            order: order.to_vec(),
            fragment_count,
        });
    }
    Ok(order.to_vec())
}

fn backward_expr_fields(d: &DistilledLayer) -> Vec<FieldKind> {
    let defaults: Vec<_> = (0..d.layer.exprs.len())
        .map(|index| {
            let expr = ExprId(index as u32);
            match &d.layer.exprs[index] {
                Expr::Source(_) => expr_field(&d.layer.exprs, &d.layer.sources, expr)
                    .unwrap_or_else(|place| {
                        *d.cross_fields.get(&place).unwrap_or_else(|| {
                            panic!("distilled layer is missing the field for {place:?}")
                        })
                    }),
                Expr::Add(_) | Expr::Mul(_) => FieldKind::Base,
            }
        })
        .collect();
    let mut fields = vec![None; d.layer.exprs.len()];
    for index in 0..d.layer.exprs.len() {
        backward_expr_field(ExprId(index as u32), d, &defaults, &mut fields);
    }
    fields.into_iter().map(Option::unwrap).collect()
}

fn backward_expr_field(
    expr: ExprId,
    d: &DistilledLayer,
    defaults: &[FieldKind],
    fields: &mut [Option<FieldKind>],
) -> FieldKind {
    if let Some(field) = fields[expr.0 as usize] {
        return field;
    }
    let field = if let Some(&field) = d.field_overrides.get(&expr) {
        field
    } else {
        match &d.layer.exprs[expr.0 as usize] {
            Expr::Source(_) => defaults[expr.0 as usize],
            Expr::Add(children) | Expr::Mul(children) => children
                .iter()
                .map(|&child| backward_expr_field(child, d, defaults, fields))
                .reduce(join)
                .unwrap_or(defaults[expr.0 as usize]),
        }
    };
    fields[expr.0 as usize] = Some(field);
    field
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, Bf, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef,
        ChallengeResolver, ClaimInfo, DagLayer, Expr, ExprId, Ext, FieldKind, LookupResolver,
        LookupValueKind, ReadPlace, ReadResolver, Resolvers, Root, RootGroup, RootOrigin, RootSlot,
        SourceId, SourceInfo, SourceKind, VirtualSetupKind, VirtualSetupResolver, eval_layer_expr,
        eval_layer_root,
    };
    use field::{Field, FieldExtension, PrimeField};

    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::bwd::fragment::{FragmentSpec, FragmentTable, MergedRecipe, ProductRecipe};
    use crate::bwd::source::BwdSpecial;
    use crate::bwd::trace::{BwdEvent, BwdServeKind};

    use super::{
        BackwardEvaluationError, compile_backward_fragments_uncached,
        elaborate_backward_fragments_driver, elaborate_backward_fragments_uncached,
    };
    use crate::eval_plan::{ConcreteBindError, EvalOp, Operand, TempId, bind_packed_plan};

    fn ext(value: u32) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
    }

    struct BackwardTestResolver;

    impl ReadResolver for BackwardTestResolver {
        fn read(&self, _place: &ReadPlace, row: usize) -> Ext {
            ext(17 + row as u32)
        }
    }

    impl LookupResolver for BackwardTestResolver {
        fn lookup(
            &self,
            _kind: &LookupValueKind,
            _set_index: usize,
            _evaluated_query: Ext,
            _row: usize,
        ) -> Bf {
            Bf::ZERO
        }
    }

    impl VirtualSetupResolver for BackwardTestResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, _row: usize) -> Bf {
            Bf::ZERO
        }
    }

    impl ChallengeResolver for BackwardTestResolver {
        fn challenge(&self, _reference: &ChallengeRef) -> Ext {
            ext(11)
        }
    }

    static BACKWARD_TEST_RESOLVER: BackwardTestResolver = BackwardTestResolver;

    fn backward_test_resolvers() -> Resolvers<'static> {
        Resolvers {
            read: &BACKWARD_TEST_RESOLVER,
            lookup: &BACKWARD_TEST_RESOLVER,
            virtual_setup: &BACKWARD_TEST_RESOLVER,
            challenge: &BACKWARD_TEST_RESOLVER,
        }
    }

    fn backward_plan_acc(out: &super::BackwardSymbolicEvaluation, d: &DistilledLayer) -> Ext {
        let resolvers = backward_test_resolvers();
        let mut acc = None;
        let mut temps = HashMap::new();
        let mut returned = None;

        for op in &out.plan.ops {
            match op {
                EvalOp::AccInit(operand) => {
                    acc = Some(backward_operand(*operand, out, d, &resolvers, &mut temps));
                }
                EvalOp::AccAdd { sign, operand } => {
                    let rhs = backward_operand(*operand, out, d, &resolvers, &mut temps);
                    let acc = acc.as_mut().expect("accumulator must be initialized");
                    match sign {
                        crate::fwd::isa::Sign::Plus => acc.add_assign(&rhs),
                        crate::fwd::isa::Sign::Minus => acc.sub_assign(&rhs),
                    };
                }
                EvalOp::AccMul(operand) => {
                    let rhs = backward_operand(*operand, out, d, &resolvers, &mut temps);
                    acc.as_mut()
                        .expect("accumulator must be initialized")
                        .mul_assign(&rhs);
                }
                EvalOp::AccFma { sign, lhs, rhs } => {
                    let mut product = backward_operand(*lhs, out, d, &resolvers, &mut temps);
                    product.mul_assign(&backward_operand(*rhs, out, d, &resolvers, &mut temps));
                    let acc = acc.as_mut().expect("accumulator must be initialized");
                    match sign {
                        crate::fwd::isa::Sign::Plus => acc.add_assign(&product),
                        crate::fwd::isa::Sign::Minus => acc.sub_assign(&product),
                    };
                }
                EvalOp::AccNeg => {
                    acc.as_mut()
                        .expect("accumulator must be initialized")
                        .negate();
                }
                EvalOp::SaveAcc(temp) => {
                    assert!(
                        temps
                            .insert(temp.id, acc.expect("accumulator must be initialized"))
                            .is_none(),
                        "temporary must be unique"
                    );
                }
                EvalOp::ReturnAcc { .. } => {
                    returned = Some(acc.expect("terminal must have an accumulator"));
                }
                EvalOp::CacheStore { .. } | EvalOp::CacheDrop(_) | EvalOp::Commit { .. } => {
                    panic!("uncached backward plan must not contain cache or commit operations")
                }
            }
        }

        returned.expect("plan must return its accumulator")
    }

    fn backward_operand(
        operand: Operand,
        out: &super::BackwardSymbolicEvaluation,
        d: &DistilledLayer,
        resolvers: &Resolvers<'_>,
        temps: &mut HashMap<TempId, Ext>,
    ) -> Ext {
        match operand {
            Operand::Source(value) => eval_layer_expr(&d.layer, value.expr, 3, resolvers),
            Operand::Temp(temp) => temps.remove(&temp.id).expect("temporary must be live"),
            Operand::Unit { negative } => {
                let mut value = Ext::ONE;
                if negative {
                    value.negate();
                }
                value
            }
            Operand::BackwardSpecial { desc } => match out.specials.get(desc) {
                Some(BwdSpecial::AccInit) => d.fragments.c_init.evaluate(&d.layer, resolvers),
                Some(BwdSpecial::Coefficient { fragment }) => d.fragments.fragments
                    [*fragment as usize]
                    .recipe
                    .evaluate(&d.layer, resolvers),
                other => {
                    panic!("backward descriptor {desc} is not a coefficient source: {other:?}")
                }
            },
            Operand::Resident(_) => panic!("uncached backward plan must not use residents"),
        }
    }

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column },
            },
        }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    fn backward_fixture() -> DistilledLayer {
        let roots = vec![
            claim_only_root(ExprId(0), 0),
            claim_only_root(ExprId(5), 1),
            claim_only_root(ExprId(3), 2),
        ];
        let layer = DagLayer {
            sources: vec![
                read_src(0),
                read_src(1),
                read_src(2),
                SourceInfo {
                    kind: SourceKind::Constant { value: 7 },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Add(vec![ExprId(1), ExprId(2)]),
                Expr::Mul(vec![ExprId(0), ExprId(4)]),
            ],
            batching: BatchingOrder {
                roots: (0..roots.len())
                    .map(|i| cs::gkr_compiler::dag_ir::RootId(i as u32))
                    .collect(),
            },
            roots,
            resolutions: BTreeMap::new(),
        };
        distill(&layer, BwdRegime::Ext, &HashMap::new(), None)
    }

    fn assert_single_uncached_terminal(out: &super::BackwardSymbolicEvaluation) {
        assert!(matches!(
            out.plan.ops.last(),
            Some(EvalOp::ReturnAcc { .. })
        ));
        assert_eq!(out.plan.stats.cache_stores, 0);
        assert_eq!(out.plan.stats.cache_hits, 0);
        assert_eq!(out.plan.stats.cache_drops, 0);
        assert_eq!(
            out.plan
                .ops
                .iter()
                .filter(|op| matches!(op, EvalOp::ReturnAcc { .. }))
                .count(),
            1
        );
    }

    #[test]
    fn backward_uncached_fragment_shape() {
        let d = backward_fixture();
        let identity: Vec<_> = (0..d.fragments.fragments.len()).collect();
        let out = elaborate_backward_fragments_uncached(&d, Some(&identity), 4, false).unwrap();
        assert_single_uncached_terminal(&out);

        let streamed = elaborate_backward_fragments_uncached(&d, Some(&identity), 4, true).unwrap();
        assert_single_uncached_terminal(&streamed);
        assert_eq!(
            out.plan.stats.dram_read_lanes,
            streamed.plan.stats.dram_read_lanes
        );
        assert_ne!(out.plan.ops, streamed.plan.ops);
        let legacy_acc = backward_plan_acc(&out, &d);
        let streamed_acc = backward_plan_acc(&streamed, &d);
        assert_eq!(legacy_acc, streamed_acc);
        let resolvers = backward_test_resolvers();
        assert_eq!(legacy_acc, eval_layer_root(&d.layer, d.root, 3, &resolvers));

        let mut reversed = identity;
        reversed.reverse();
        let out = elaborate_backward_fragments_uncached(&d, Some(&reversed), 4, false).unwrap();
        assert_single_uncached_terminal(&out);
    }

    #[test]
    fn backward_uncached_coeff_and_c_init() {
        let d = backward_fixture();
        assert!(!d.fragments.c_init.terms.is_empty());
        assert!(
            d.fragments
                .fragments
                .iter()
                .any(|fragment| !fragment.recipe.is_trivial())
        );

        let out = elaborate_backward_fragments_uncached(&d, None, 4, false).unwrap();
        let EvalOp::AccInit(Operand::BackwardSpecial { desc }) = out.plan.ops[0] else {
            panic!("non-empty c_init must initialize the accumulator through its descriptor")
        };
        assert_eq!(out.specials.get(desc), Some(&BwdSpecial::AccInit));
        assert_eq!(
            out.plan
                .ops
                .iter()
                .filter(|op| matches!(
                    op,
                    EvalOp::AccMul(Operand::BackwardSpecial { desc })
                        if matches!(out.specials.get(*desc), Some(BwdSpecial::Coefficient { .. }))
                ))
                .count(),
            1,
            "the non-trivial fragment recipe must use one coefficient operand"
        );
        assert!(matches!(
            bind_packed_plan(&out.packed, &d.layer, &[d.root], 0, 16),
            Err(ConcreteBindError::BackwardSpecialRequiresBindings { .. })
        ));
    }

    #[test]
    fn backward_uncached_binds_coefficient_specials() {
        let d = backward_fixture();

        let out = compile_backward_fragments_uncached(&d, None, 4, false).unwrap();

        assert!(
            out.compiled
                .program
                .instrs
                .iter()
                .any(|instruction| match instruction {
                    crate::fwd::isa::Instr::Mov {
                        src: Some(crate::fwd::isa::OperandLine::Special { desc }),
                        ..
                    } => matches!(out.compiled.specials.get(*desc), Some(BwdSpecial::AccInit)),
                    _ => false,
                })
        );
        assert!(
            out.compiled
                .program
                .instrs
                .iter()
                .any(|instruction| match instruction {
                    crate::fwd::isa::Instr::Mul { operands, .. } =>
                        operands.iter().any(|operand| {
                            matches!(
                                operand,
                                crate::fwd::isa::OperandLine::Special { desc }
                                    if matches!(
                                        out.compiled.specials.get(*desc),
                                        Some(BwdSpecial::Coefficient { .. })
                                    )
                            )
                        }),
                    _ => false,
                })
        );
    }

    #[test]
    fn backward_uncached_rejects_invalid_order() {
        let d = backward_fixture();
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, Some(&[0, 0]), 4, false),
            Err(BackwardEvaluationError::InvalidFragmentOrder { .. })
        ));
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, Some(&[0, 2]), 4, false),
            Err(BackwardEvaluationError::InvalidFragmentOrder { .. })
        ));
    }

    #[test]
    fn backward_uncached_rejects_empty_decomposition() {
        let mut d = backward_fixture();
        d.fragments = FragmentTable::default();
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, None, 4, false),
            Err(BackwardEvaluationError::EmptyFragmentDecomposition)
        ));
    }

    #[test]
    fn backward_uncached_infers_cross_layer_read_field() {
        let place = ReadPlace::CacheOutput {
            layer: 0,
            offset: 0,
        };
        let layer = DagLayer {
            sources: vec![SourceInfo {
                kind: SourceKind::Read {
                    place: place.clone(),
                },
            }],
            exprs: vec![Expr::Source(SourceId(0))],
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(ExprId(0), 0)],
            resolutions: BTreeMap::new(),
        };
        let cross = HashMap::from([(place, FieldKind::Ext)]);
        let d = distill(&layer, BwdRegime::R0, &cross, None);

        let out = compile_backward_fragments_uncached(&d, None, 4, false).unwrap();
        let EvalOp::AccInit(Operand::Source(value)) = out.symbolic.plan.ops[0] else {
            panic!("single read fragment must initialize from its source")
        };
        assert_eq!(value.field, FieldKind::Ext);
    }

    #[test]
    fn backward_legacy_reduction_keeps_final_child_in_accumulator() {
        let sources = (0..5)
            .map(|column| SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::CacheOutput {
                        layer: 0,
                        offset: column,
                    },
                },
            })
            .collect::<Vec<_>>();
        let mut exprs = (0..5)
            .map(|source| Expr::Source(SourceId(source)))
            .collect::<Vec<_>>();
        exprs.push(Expr::Add((0..5).map(ExprId).collect()));
        let layer = DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(ExprId(5), 0)],
            resolutions: BTreeMap::new(),
        };
        let cross = (0..5)
            .map(|offset| (ReadPlace::CacheOutput { layer: 0, offset }, FieldKind::Ext))
            .collect();
        let mut d = distill(&layer, BwdRegime::R0, &cross, None);
        let root_expr = d.layer.roots[d.root.0 as usize].expr;
        d.fragments = FragmentTable {
            fragments: vec![FragmentSpec {
                atoms: vec![root_expr],
                recipe: MergedRecipe {
                    terms: vec![ProductRecipe::default()],
                },
            }],
            c_init: MergedRecipe::default(),
        };

        let out = compile_backward_fragments_uncached(&d, None, 4, false).unwrap();

        assert!(out.compiled.stats.max_live_cells <= 16);
    }

    #[test]
    fn backward_legacy_reduction_evaluates_deep_cone_before_stash() {
        let challenge = || SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::ClaimBatching,
                    power: ChallengePower::One,
                },
            },
        };
        let sources = vec![
            challenge(),
            SourceInfo {
                kind: SourceKind::Constant { value: 1 },
            },
            SourceInfo {
                kind: SourceKind::VirtualSetup {
                    kind: VirtualSetupKind::InitsAndTeardownsLow,
                },
            },
            challenge(),
            SourceInfo {
                kind: SourceKind::VirtualSetup {
                    kind: VirtualSetupKind::InitsAndTeardownsHigh,
                },
            },
            challenge(),
            SourceInfo {
                kind: SourceKind::Constant { value: 1024 },
            },
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Mul(vec![ExprId(2), ExprId(3)]),
            Expr::Source(SourceId(4)),
            Expr::Source(SourceId(5)),
            Expr::Mul(vec![ExprId(5), ExprId(6)]),
            Expr::Add(vec![ExprId(0), ExprId(1), ExprId(4), ExprId(7)]),
            Expr::Source(SourceId(6)),
            Expr::Add(vec![ExprId(5), ExprId(9)]),
            Expr::Mul(vec![ExprId(6), ExprId(10)]),
            Expr::Add(vec![ExprId(0), ExprId(1), ExprId(4), ExprId(11)]),
        ];
        let root_expr = ExprId(12);
        let layer = DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(root_expr, 0)],
            resolutions: BTreeMap::new(),
        };
        let fields = vec![
            FieldKind::Ext,
            FieldKind::Base,
            FieldKind::Base,
            FieldKind::Ext,
            FieldKind::Ext,
            FieldKind::Base,
            FieldKind::Ext,
            FieldKind::Ext,
            FieldKind::Ext,
            FieldKind::Base,
            FieldKind::Base,
            FieldKind::Ext,
            FieldKind::Ext,
        ];
        let fragments = [FragmentSpec {
            atoms: vec![root_expr],
            recipe: MergedRecipe {
                terms: vec![ProductRecipe::default()],
            },
        }];

        let out = elaborate_backward_fragments_driver(
            &layer,
            cs::gkr_compiler::dag_ir::RootId(0),
            &fields,
            &fragments,
            &[0],
            &[None],
            Some(0),
            16,
            false,
        );

        assert!(out.is_ok(), "legacy reduction should fit b16: {out:?}");
    }

    #[test]
    fn backward_trace_names_fused_product_consumers() {
        let layer = DagLayer {
            sources: (0..4).map(read_src).collect(),
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Mul(vec![ExprId(2), ExprId(3)]),
                Expr::Add(vec![ExprId(1), ExprId(4)]),
                Expr::Mul(vec![ExprId(0), ExprId(5)]),
            ],
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(ExprId(6), 0)],
            resolutions: BTreeMap::new(),
        };
        let d = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        let (term, add) = d
            .fragments
            .fragments
            .iter()
            .enumerate()
            .flat_map(|(term, fragment)| fragment.atoms.iter().map(move |&atom| (term, atom)))
            .find(|(_, atom)| matches!(d.layer.exprs[atom.0 as usize], Expr::Add(_)))
            .expect("the opaque product keeps its nested add atom");
        let Expr::Add(add_children) = &d.layer.exprs[add.0 as usize] else {
            unreachable!()
        };
        let product = *add_children
            .iter()
            .find(|child| matches!(d.layer.exprs[child.0 as usize], Expr::Mul(_)))
            .expect("the nested add has a direct binary product");
        let Expr::Mul(product_children) = &d.layer.exprs[product.0 as usize] else {
            unreachable!()
        };

        let out = compile_backward_fragments_uncached(&d, None, 4, true).unwrap();
        let serves = out
            .trace
            .events
            .iter()
            .filter_map(|event| match event {
                BwdEvent::Serve { fp, .. } => Some(*fp),
                _ => None,
            })
            .collect::<Vec<_>>();

        assert!(serves.iter().any(|fp| {
            fp.term == term as u32
                && fp.kind == BwdServeKind::Operand
                && fp.value == add
                && fp.consumer.is_none()
        }));
        assert!(serves.iter().any(|fp| {
            fp.term == term as u32 && fp.value == product && fp.consumer == Some(add)
        }));
        for child in product_children {
            assert!(serves.iter().any(|fp| {
                fp.term == term as u32 && fp.value == *child && fp.consumer == Some(product)
            }));
        }
    }
}
