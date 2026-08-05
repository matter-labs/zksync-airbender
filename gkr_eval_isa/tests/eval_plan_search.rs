//! On-demand measurement probe for the alternative evaluation-plan search.
//!
//! Search and corpus measurements are ignored because they lower committed
//! circuit fixtures and score populations. Run them explicitly with:
//! `cargo test -p gkr_eval_isa --test eval_plan_search -- --ignored --nocapture`.
//! The corpus probe accepts `EVAL_PLAN_CIRCUIT`, comma-separated
//! `EVAL_PLAN_BUDGET` (comma-separated cell counts), and `EVAL_PLAN_EVALUATIONS` filters; release mode is
//! recommended for searches.

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

use gkr_eval_ir::{DagLayer, Expr, ExprId, FieldKind, RootGroup, SourceKind, lower_dag, validate};
use gkr_eval_isa::LayerSchedule;
use gkr_eval_isa::eval_plan::{
    CacheOracle, CacheStateView, EvaluationArtifactError, EvaluationCompileError, EvaluationGenome,
    EvaluationGenomeArtifact, EvaluationGenomeCircuitArtifact, EvaluationLayoutVariant,
    EvaluationUnitKey, GenomeOracle, MutationSearchConfig, PackConfig, PlanSearchContext,
    RetentionPreference, RootKey, SearchProvenance, SiteId, StructuralSiteIndex, bind_packed_plan,
    bind_packed_plan_with_actions, compile_circuit_with_evaluation_genomes,
    compile_layer_with_evaluation_genome, elaborate_with_oracle_and_sinks, interpret_packed_plan,
    interpret_plan, load_evaluation_genome_artifact, mutation_search, pack_plan,
    produce_searched_evaluation_genome_artifact, structural_fingerprints,
};
use gkr_eval_isa::fwd::compile::{
    build_cross_layer_field_map, compile_circuit, expr_operand_field, load_committed_schedule,
};
use gkr_eval_isa::fwd::context::{
    CompiledLayer, ForwardAction, OutputCell, RootOutput, build_forward_actions,
};
use gkr_eval_isa::fwd::disasm::disassemble_layer;
use gkr_eval_isa::fwd::interp::interpret_layer_row;
use gkr_eval_isa::fwd::isa::{Instr, OperandField, Program};
use gkr_eval_isa::fwd::validate::validate_compiled;
use gkr_eval_isa::schedule_search::genome::Genome as ReferenceGenome;
use gkr_eval_isa::schedule_search::scorer::{
    LayerCtx, genome_from_schedule, score as score_reference,
};

const ADD_SUB: &str = "add_sub_lui_auipc_mop_layout_gkr.json";
const ADD_SUB_EVAL_PLAN: &str = "add_sub_lui_auipc_mop_with_caches_fwd_eval_plan_c4_gkr.json";
const FORWARD_CORPUS: &[(&str, &str)] = &[
    ("add_sub_lui_auipc_mop", ADD_SUB),
    (
        "bigint_with_extended_control",
        "bigint_with_extended_control_layout_gkr.json",
    ),
    ("blake2_g_function", "blake2_g_function_layout_gkr.json"),
    (
        "blake2_with_extended_control",
        "blake2_with_extended_control_layout_gkr.json",
    ),
    ("inits_and_teardowns", "inits_and_teardowns_layout_gkr.json"),
    ("jump_branch_slt", "jump_branch_slt_layout_gkr.json"),
    ("keccak_special5", "keccak_special5_layout_gkr.json"),
    ("mem_subword_only", "mem_subword_only_layout_gkr.json"),
    ("mem_word_only", "mem_word_only_layout_gkr.json"),
    ("shift_binop", "shift_binop_layout_gkr.json"),
    ("unsigned_mul_div", "unsigned_mul_div_layout_gkr.json"),
];

fn evaluation_artifact_path(circuit: &str) -> std::path::PathBuf {
    common::compiled_circuit_dir().join(format!("{circuit}_with_caches_fwd_eval_plan_c4_gkr.json"))
}

fn pin_digest(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |digest, byte| {
        (digest ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

fn arithmetic_arities(program: &Program) -> [usize; 3] {
    let mut totals = [0; 3];
    for instr in &program.instrs {
        match instr {
            Instr::Add { operands, .. } => totals[0] += operands.len(),
            Instr::Mul { operands, .. } => totals[1] += operands.len(),
            Instr::Fma { pairs, .. } => totals[2] += pairs.len(),
            Instr::Mov { .. } => {}
        }
    }
    totals
}

fn root_segment_op_counts(compiled: &CompiledLayer) -> BTreeMap<gkr_eval_ir::RootId, [usize; 4]> {
    let mut roots_by_destination = BTreeMap::<(u8, u16), Vec<_>>::new();
    for &(root, output) in &compiled.root_outputs {
        if let RootOutput::Cell(OutputCell::Global { slot, col }) = output {
            roots_by_destination
                .entry((slot, col))
                .or_default()
                .push(root);
        }
    }

    let mut result = BTreeMap::new();
    let mut counts = [0usize; 4]; // [mov, add, mul, fma]
    for instr in &compiled.program.instrs {
        let destination = match instr {
            Instr::Mov { dst, .. } => {
                counts[0] += 1;
                match dst {
                    Some(gkr_eval_isa::fwd::isa::DstLine::GlobalMaterialize { slot, col }) => {
                        Some((*slot, *col))
                    }
                    _ => None,
                }
            }
            Instr::Add { .. } => {
                counts[1] += 1;
                None
            }
            Instr::Mul { .. } => {
                counts[2] += 1;
                None
            }
            Instr::Fma { .. } => {
                counts[3] += 1;
                None
            }
        };
        let Some(roots) =
            destination.and_then(|destination| roots_by_destination.get(&destination))
        else {
            continue;
        };
        for &root in roots {
            result.insert(root, counts);
        }
        counts = [0; 4];
    }
    result
}

fn report_root_segment_diff(
    layer: &DagLayer,
    established: &CompiledLayer,
    candidate: &CompiledLayer,
) {
    let established = root_segment_op_counts(established);
    let candidate = root_segment_op_counts(candidate);
    let roots = established
        .keys()
        .chain(candidate.keys())
        .copied()
        .collect::<BTreeSet<_>>();
    for root in roots {
        let established = established.get(&root).copied().unwrap_or_default();
        let candidate = candidate.get(&root).copied().unwrap_or_default();
        if established != candidate {
            println!(
                "root-segment-diff: root={} expr={} established=[mov,add,mul,fma]={established:?} \
                 candidate={candidate:?}",
                root.0, layer.roots[root.0 as usize].expr.0,
            );
        }
    }
}

fn scalar_isa_ops(program: &Program) -> usize {
    program
        .instrs
        .iter()
        .map(|instr| match instr {
            Instr::Add { operands, .. } => operands.len(),
            Instr::Mul {
                negate_acc,
                operands,
                ..
            } => operands.len() + usize::from(*negate_acc),
            Instr::Fma { pairs, .. } => pairs.len(),
            Instr::Mov { .. } => 0,
        })
        .sum()
}

fn report_expr(layer: &DagLayer, expr: ExprId, label: &str) {
    fn visit(layer: &DagLayer, expr: ExprId, seen: &mut BTreeSet<ExprId>) {
        if !seen.insert(expr) {
            return;
        }
        match &layer.exprs[expr.0 as usize] {
            Expr::Source(source) => println!(
                "eval-plan repro-expr: expr={} source={:?}",
                expr.0, layer.sources[source.0 as usize].kind
            ),
            Expr::Add(children) => {
                println!(
                    "eval-plan repro-expr: expr={} add={:?}",
                    expr.0,
                    children.iter().map(|child| child.0).collect::<Vec<_>>()
                );
                for &child in children {
                    visit(layer, child, seen);
                }
            }
            Expr::Mul(children) => {
                println!(
                    "eval-plan repro-expr: expr={} mul={:?}",
                    expr.0,
                    children.iter().map(|child| child.0).collect::<Vec<_>>()
                );
                for &child in children {
                    visit(layer, child, seen);
                }
            }
        }
    }

    println!("eval-plan repro-{label}: expr={}", expr.0);
    visit(layer, expr, &mut BTreeSet::new());
}

fn report_expr_cone(layer: &DagLayer, root: gkr_eval_ir::RootId) {
    let expr = layer.roots[root.0 as usize].expr;
    report_expr(layer, expr, &format!("root-{}", root.0));
}

fn report_plan_attribution(
    stem: &str,
    layer_index: usize,
    budget: usize,
    layer: &DagLayer,
    plan: &gkr_eval_isa::eval_plan::EvalPlan,
) {
    if std::env::var_os("EVAL_PLAN_OPS").is_some() {
        for (index, op) in plan.ops.iter().enumerate() {
            println!(
                "eval-plan op: circuit={stem} layer={layer_index} budget={budget} index={index} {op:?}"
            );
        }
    }
    let mut rows = plan
        .attribution
        .iter()
        .filter_map(|(&expr, attribution)| {
            let (kind, arity, effective_arity, binary_product, children) =
                match &layer.exprs[expr.0 as usize] {
                    Expr::Source(_) => return None,
                    Expr::Add(children) => (
                        "add",
                        children.len(),
                        children.len(),
                        false,
                        children.iter().map(|child| child.0).collect::<Vec<_>>(),
                    ),
                    Expr::Mul(children) => {
                        let effective = children
                            .iter()
                            .filter(|&&child| {
                                let Expr::Source(source) = &layer.exprs[child.0 as usize] else {
                                    return true;
                                };
                                !matches!(
                                    layer.sources[source.0 as usize].kind,
                                    SourceKind::Constant {
                                        value: 1 | 0x7800_0000
                                    }
                                )
                            })
                            .count();
                        (
                            "mul",
                            children.len(),
                            effective,
                            effective == 2,
                            children.iter().map(|child| child.0).collect::<Vec<_>>(),
                        )
                    }
                };
            let replay = if attribution.computations > 1 {
                attribution.arithmetic_ops - attribution.arithmetic_ops / attribution.computations
            } else {
                0
            };
            let unfused_binary_adds = if binary_product {
                attribution
                    .additive_demands
                    .saturating_sub(attribution.fma_fusions)
            } else {
                0
            };
            ((
                replay,
                unfused_binary_adds,
                attribution.arithmetic_ops,
                attribution.fma_fusions,
                attribution.signed_add_fusions,
            ) != (0, 0, 0, 0, 0))
                .then_some((
                    replay,
                    unfused_binary_adds,
                    attribution.arithmetic_ops,
                    expr,
                    kind,
                    arity,
                    effective_arity,
                    children,
                    *attribution,
                ))
        })
        .collect::<Vec<_>>();
    let total_replay = rows.iter().map(|row| row.0).sum::<usize>();
    let total_unfused = rows.iter().map(|row| row.1).sum::<usize>();
    let total_arithmetic = rows.iter().map(|row| row.2).sum::<usize>();
    let total_fma = plan
        .attribution
        .values()
        .map(|attribution| attribution.fma_fusions)
        .sum::<usize>();
    println!(
        "eval-plan attribution-summary: circuit={stem} layer={layer_index} budget={budget} \
         replay_ops={total_replay} arithmetic={total_arithmetic} fma={total_fma} \
         unfused_binary_adds={total_unfused}"
    );
    for row in rows.iter().filter(|row| row.1 != 0) {
        let parents = layer
            .exprs
            .iter()
            .enumerate()
            .filter_map(|(parent, candidate)| match candidate {
                Expr::Add(children) if children.contains(&row.3) => Some((
                    parent as u32,
                    "add",
                    children.iter().map(|child| child.0).collect::<Vec<_>>(),
                )),
                Expr::Mul(children) if children.contains(&row.3) => Some((
                    parent as u32,
                    "mul",
                    children.iter().map(|child| child.0).collect::<Vec<_>>(),
                )),
                _ => None,
            })
            .collect::<Vec<_>>();
        println!(
            "eval-plan unfused-product: circuit={stem} layer={layer_index} budget={budget} \
             expr={} raw_arity={} effective_arity={} children={:?} parents={parents:?} \
             additive_demands={} fma={} seeds={} unready={} resident={} preserved={} \
             computations={} stores={} materializations={}",
            row.3.0,
            row.5,
            row.6,
            row.7,
            row.8.additive_demands,
            row.8.fma_fusions,
            row.8.accumulator_seeds,
            row.8.unready_product_adds,
            row.8.resident_product_adds,
            row.8.preserved_product_adds,
            row.8.computations,
            row.8.cache_stores,
            row.8.materializations,
        );
    }
    rows.sort_by_key(|row| std::cmp::Reverse((row.0, row.1, row.2, row.3.0)));
    for (rank, (replay, unfused, _, expr, kind, arity, effective_arity, children, attribution)) in
        rows.into_iter().take(12).enumerate()
    {
        println!(
            "eval-plan attribution: circuit={stem} layer={layer_index} budget={budget} \
             rank={} expr={} kind={kind} raw_arity={arity} effective_arity={effective_arity} \
             children={children:?} \
             demands={} additive_demands={} \
             computations={} replay_ops={replay} resident_hits={} arithmetic={} seeds={} \
             fma={} signed_add={} unfused_binary_adds={unfused} stores={} materializations={}",
            rank + 1,
            expr.0,
            attribution.demands,
            attribution.additive_demands,
            attribution.computations,
            attribution.resident_hits,
            attribution.arithmetic_ops,
            attribution.accumulator_seeds,
            attribution.fma_fusions,
            attribution.signed_add_fusions,
            attribution.cache_stores,
            attribution.materializations,
        );
    }
}

/// Established neutral-policy semantics: cache a reusable DRAM-reaching value
/// when space is free, never evict an equally useful live resident merely to
/// admit a new value, and drop residents once they have no future demand.
struct FirstFitOracle<'a> {
    index: &'a StructuralSiteIndex,
    active: Vec<bool>,
}

impl<'a> FirstFitOracle<'a> {
    fn new(index: &'a StructuralSiteIndex) -> Self {
        Self {
            index,
            active: vec![true; index.len()],
        }
    }

    fn active_site_count(&self) -> usize {
        self.active.iter().filter(|&&active| active).count()
    }

    fn is_descendant(candidate: &SiteId, ancestor: &SiteId) -> bool {
        candidate.root == ancestor.root
            && candidate.path.len() > ancestor.path.len()
            && candidate.path.starts_with(&ancestor.path)
    }
}

impl CacheOracle for FirstFitOracle<'_> {
    fn desired_after(
        &mut self,
        site: &SiteId,
        entry: CacheStateView<'_>,
    ) -> Vec<RetentionPreference> {
        let index = self
            .index
            .position(site)
            .expect("first-fit site is indexed");
        assert!(self.active[index], "first-fit site visited twice");
        self.active[index] = false;
        if entry
            .residents
            .iter()
            .any(|resident| resident.fingerprint == site.value)
        {
            for (index, candidate) in self.index.sites().iter().enumerate() {
                if self.active[index] && Self::is_descendant(candidate, site) {
                    self.active[index] = false;
                }
            }
        }

        let mut after = BTreeMap::new();
        for (index, candidate) in self.index.sites().iter().enumerate() {
            if self.active[index] && !Self::is_descendant(candidate, site) {
                *after.entry(candidate.value).or_insert(0usize) += 1;
            }
        }
        let mut candidates = BTreeMap::<_, (usize, f64)>::new();
        candidates.insert(site.value, (1, 1.0));
        for resident in entry.residents {
            candidates.insert(resident.fingerprint, (1, 2.0));
        }
        for (index, candidate) in self.index.sites().iter().enumerate() {
            if self.active[index] && Self::is_descendant(candidate, site) {
                candidates.entry(candidate.value).or_insert((1, 1.0));
            }
        }
        candidates
            .into_iter()
            .filter_map(|(value, (required, priority))| {
                let count = after.get(&value).copied().unwrap_or(0);
                let profile = self.index.profile(value)?;
                (count >= required && profile.recompute_dram_lanes > 0)
                    .then_some(RetentionPreference { value, priority })
            })
            .collect()
    }
}

fn root_group_key(group: &RootGroup) -> u8 {
    match group {
        RootGroup::Gates => 0,
        RootGroup::GatesExternal => 1,
    }
}

fn committed_order_keys(context: &PlanSearchContext<'_>, schedule: &LayerSchedule) -> Vec<f64> {
    let ranks = schedule
        .units
        .iter()
        .enumerate()
        .map(|(rank, unit)| ((root_group_key(&unit.group), unit.relation_index), rank))
        .collect::<BTreeMap<_, _>>();
    let standalone_start = schedule.units.len();
    context
        .units()
        .iter()
        .enumerate()
        .map(|(canonical_index, unit)| match &unit.key {
            EvaluationUnitKey::Relation {
                group,
                relation_index,
            } => *ranks
                .get(&(root_group_key(group), *relation_index))
                .unwrap_or_else(|| {
                    panic!("committed schedule is missing relation ({group:?}, {relation_index})")
                }) as f64,
            EvaluationUnitKey::Standalone(_) => (standalone_start + canonical_index) as f64,
        })
        .collect()
}

/// Translate the established schedule into the stable-site genome as closely
/// as its older identity permits. Unit order is exact. Cache priorities are
/// matched by semantic root and value; when the old schedule distinguishes
/// multiple consumer slots for the same root/value, the maximum priority is
/// used for every corresponding stable-path occurrence.
fn compatible_genome_from_schedule(
    context: &PlanSearchContext<'_>,
    layer: &DagLayer,
    schedule: &LayerSchedule,
) -> EvaluationGenome {
    let fingerprints = structural_fingerprints(layer).expect("fingerprint compatible schedule");
    let mut priorities = HashMap::<(RootKey, _), f64>::new();
    for &(site, priority) in &schedule.sites {
        let root = &layer.roots[site.root.0 as usize];
        let root_key = RootKey {
            expr: fingerprints[root.expr.0 as usize],
            materialize: root.materialize.clone(),
            claim_origin: root.claim.as_ref().map(|claim| claim.origin.clone()),
        };
        priorities
            .entry((root_key, fingerprints[site.value.0 as usize]))
            .and_modify(|current| *current = current.max(priority))
            .or_insert(priority);
    }

    let mut genome = EvaluationGenome::neutral(context);
    genome.root_order_key = committed_order_keys(context, schedule);
    for (gene, site) in genome
        .cache_priority
        .iter_mut()
        .zip(context.site_index().sites())
    {
        *gene = priorities
            .get(&(site.root.clone(), site.value))
            .copied()
            .unwrap_or(0.0);
    }
    genome
}

fn score_first_fit(
    layer: &DagLayer,
    fields: &[FieldKind],
    context: &PlanSearchContext<'_>,
    order_keys: &[f64],
    budget: usize,
) -> (usize, usize, usize, usize, usize) {
    let root_order = context
        .decode_root_order(order_keys)
        .expect("decode first-fit root order");
    let mut oracle = FirstFitOracle::new(context.site_index());
    let plan = elaborate_with_oracle_and_sinks(
        layer,
        fields,
        &root_order,
        context.materialized_roots(),
        budget,
        &mut oracle,
    )
    .expect("elaborate first-fit plan");
    assert_eq!(
        oracle.active_site_count(),
        0,
        "first-fit sites remain active"
    );
    let packed = pack_plan(&plan, layer, PackConfig::default()).expect("pack first-fit plan");
    let concrete = bind_packed_plan(&packed, layer, context.materialized_roots(), 0, budget)
        .expect("bind first-fit plan");
    assert_eq!(
        concrete.compiled.stats.dram_traffic, plan.stats.dram_read_lanes,
        "first-fit concrete traffic"
    );
    (
        plan.stats.dram_read_lanes,
        plan.stats.cache_stores,
        plan.stats.cache_hits,
        plan.stats.cache_drops,
        concrete.stats.relocation_moves,
    )
}

fn capture_retentive_circuit_artifact(
    circuit: &str,
    layout_fixture: &str,
    dag: &gkr_eval_ir::DagCircuit,
    layout: &cs::gkr_compiler::GKRCircuitArtifact<field::baby_bear::base::BabyBearField>,
) -> EvaluationGenomeCircuitArtifact {
    const BUDGET_CELLS: usize = 4;

    let cross = build_cross_layer_field_map(dag);
    let layers = dag
        .layers
        .iter()
        .zip(&layout.layers)
        .enumerate()
        .map(|(layer_index, (layer, layout_layer))| {
            let fields = (0..layer.exprs.len())
                .map(
                    |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                        OperandField::Base => FieldKind::Base,
                        OperandField::Ext => FieldKind::Ext,
                    },
                )
                .collect::<Vec<_>>();
            let actions = build_forward_actions(layer, layout_layer, &layout.scratch_space_mapping)
                .unwrap_or_else(|error| panic!("classify add_sub layer {layer_index}: {error:?}"));
            let compute_roots = actions
                .iter()
                .filter_map(|(&root, action)| {
                    matches!(action, ForwardAction::Compute).then_some(root)
                })
                .collect::<Vec<_>>();
            let context = PlanSearchContext::build_for_roots(
                layer,
                &fields,
                layout_layer.layer,
                BUDGET_CELLS,
                &compute_roots,
            )
            .unwrap_or_else(|error| panic!("build add_sub layer {layer_index} context: {error:?}"));
            EvaluationGenomeArtifact::capture(
                circuit,
                &context,
                &actions,
                EvaluationGenome::retentive(&context),
            )
            .unwrap_or_else(|error| {
                panic!("capture add_sub layer {layer_index} artifact: {error:?}")
            })
        })
        .collect();
    EvaluationGenomeCircuitArtifact::new(
        circuit,
        EvaluationLayoutVariant::WithCaches,
        layout_fixture,
        BUDGET_CELLS,
        SearchProvenance {
            algorithm: "retentive-smoke".to_owned(),
            seed: 0,
            evaluations: 0,
            staging_evaluations: 0,
        },
        layers,
    )
    .expect("build add_sub circuit artifact")
}

#[test]
fn evaluation_artifact_json_uses_only_cell_budget() {
    let layout = common::load_fixture(ADD_SUB);
    let dag = lower_dag(&layout).expect("lower add_sub fixture");
    let artifact =
        capture_retentive_circuit_artifact("add_sub_lui_auipc_mop", ADD_SUB, &dag, &layout);
    let json = serde_json::to_value(&artifact).expect("serialize evaluation artifact");

    assert_eq!(
        json.get("budget_cells").and_then(serde_json::Value::as_u64),
        Some(4)
    );
    assert!(json.get("budget_lanes").is_none());
    assert!(json.get("schema_version").is_none());
    for layer in json["layers"].as_array().expect("artifact layers") {
        assert_eq!(
            layer
                .get("budget_cells")
                .and_then(serde_json::Value::as_u64),
            Some(4),
        );
        assert!(layer.get("budget_lanes").is_none());
        assert!(layer.get("schema_version").is_none());
    }
}

#[test]
fn forward_search_observable_pins() {
    let layout = common::load_fixture(ADD_SUB);
    let dag = lower_dag(&layout).expect("lower add_sub fixture");
    validate(&dag).expect("validate add_sub DAG");
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];
    let artifact_layer = &layout.layers[0];
    let fields = (0..layer.exprs.len())
        .map(
            |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                OperandField::Base => FieldKind::Base,
                OperandField::Ext => FieldKind::Ext,
            },
        )
        .collect::<Vec<_>>();
    let actions = build_forward_actions(layer, artifact_layer, &layout.scratch_space_mapping)
        .expect("classify add_sub layer zero roots");
    let compute_roots = actions
        .iter()
        .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
        .collect::<Vec<_>>();
    let context =
        PlanSearchContext::build_for_roots(layer, &fields, artifact_layer.layer, 4, &compute_roots)
            .expect("build add_sub layer zero search context");

    let mut sequence = Vec::new();
    let mut selected = None;
    for evaluations in [2, 4, 8, 16, 32, 64, 128] {
        let outcome = mutation_search(
            &context,
            MutationSearchConfig {
                population: 16,
                evaluations,
                staging_evaluations: 0,
                seed: 0,
                cache_mutations: 2,
            },
        )
        .unwrap_or_else(|error| panic!("search add_sub layer zero at {evaluations}: {error:?}"));
        let genome = serde_json::to_string(&outcome.best_genome)
            .expect("serialize selected add_sub layer zero genome");
        println!(
            "CANDIDATE evaluations={evaluations} fitness={:?} genome={genome}",
            outcome.best.fitness,
        );
        sequence.extend_from_slice(&evaluations.to_le_bytes());
        sequence.extend_from_slice(genome.as_bytes());
        selected = Some(outcome.best_genome);
    }

    let selected = selected.expect("search checkpoints are nonempty");
    let selected_json = serde_json::to_string(&selected).expect("serialize selected genome");
    println!("SELECTED-GENOME {selected_json}");
    let selected_artifact =
        EvaluationGenomeArtifact::capture("add_sub_lui_auipc_mop", &context, &actions, selected)
            .expect("capture selected add_sub layer zero artifact");
    let artifact_bytes =
        serde_json::to_vec(&selected_artifact).expect("serialize selected artifact");
    let artifact_digest = pin_digest(&artifact_bytes);
    assert_eq!(artifact_bytes.len(), 2301);
    assert_eq!(artifact_digest, 0xec0c_fb25_c726_1db3);
    println!(
        "ARTIFACT-BYTES len={} fnv={:016x}",
        artifact_bytes.len(),
        artifact_digest,
    );
    sequence.extend_from_slice(&artifact_bytes);
    let sequence_digest = pin_digest(&sequence);
    assert_eq!(sequence_digest, 0xcfd0_9b81_2aad_09f0);
    println!("DIGEST {sequence_digest:016x}");
}

#[test]
fn add_sub_artifact_compiles_and_matches_canonical_values() {
    const BUDGET_CELLS: usize = 4;
    const BUDGET_LANES: usize = 16;

    let artifact = common::load_fixture(ADD_SUB);
    let dag = lower_dag(&artifact).expect("lower add_sub fixture");
    validate(&dag).expect("validate add_sub DAG");
    assert_eq!(dag.layers.len(), artifact.layers.len());
    let cross = build_cross_layer_field_map(&dag);
    let synthetic = common::SyntheticResolvers;
    let resolvers = common::resolvers(&synthetic);
    let mut exercised_nonzero_layer = false;
    let mut layer_artifacts = Vec::with_capacity(dag.layers.len());
    for (layer_index, (layer, artifact_layer)) in
        dag.layers.iter().zip(&artifact.layers).enumerate()
    {
        let fields = (0..layer.exprs.len())
            .map(
                |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                    OperandField::Base => FieldKind::Base,
                    OperandField::Ext => FieldKind::Ext,
                },
            )
            .collect::<Vec<_>>();
        let actions = build_forward_actions(layer, artifact_layer, &artifact.scratch_space_mapping)
            .unwrap_or_else(|error| {
                panic!("classify add_sub layer {layer_index} roots: {error:?}")
            });
        let compute_roots = actions
            .iter()
            .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
            .collect::<Vec<_>>();
        exercised_nonzero_layer |= layer_index != 0 && !compute_roots.is_empty();

        let context = PlanSearchContext::build_for_roots(
            layer,
            &fields,
            artifact_layer.layer,
            BUDGET_CELLS,
            &compute_roots,
        )
        .unwrap_or_else(|error| {
            panic!("build add_sub layer {layer_index} evaluation-plan context: {error:?}")
        });
        let genome = EvaluationGenome::retentive(&context);
        let scored = context.score(&genome).unwrap_or_else(|error| {
            panic!("score add_sub layer {layer_index} retentive plan: {error:?}")
        });
        let plan = scored
            .plan
            .as_ref()
            .unwrap_or_else(|| panic!("layer {layer_index} retentive plan is feasible"));
        let packed = pack_plan(plan, layer, PackConfig::default())
            .unwrap_or_else(|error| panic!("pack add_sub layer {layer_index}: {error:?}"));
        let genome_artifact =
            EvaluationGenomeArtifact::capture("add_sub_lui_auipc_mop", &context, &actions, genome)
                .unwrap_or_else(|error| {
                    panic!("capture add_sub layer {layer_index} genome artifact: {error:?}")
                });
        let encoded_artifact = serde_json::to_string(&genome_artifact)
            .unwrap_or_else(|error| panic!("serialize layer {layer_index} artifact: {error}"));
        let decoded_artifact: EvaluationGenomeArtifact = serde_json::from_str(&encoded_artifact)
            .unwrap_or_else(|error| panic!("deserialize layer {layer_index} artifact: {error}"));
        assert_eq!(decoded_artifact, genome_artifact);
        if layer_index == 0 {
            let mut stale = decoded_artifact.clone();
            stale.budget_cells -= 1;
            assert!(matches!(
                stale.validate_against("add_sub_lui_auipc_mop", &context, &actions),
                Err(EvaluationArtifactError::BudgetCellsMismatch { .. })
            ));
            let mut wrong_domain = decoded_artifact.clone();
            wrong_domain.site_domain.count -= 1;
            assert!(matches!(
                wrong_domain.validate_against("add_sub_lui_auipc_mop", &context, &actions),
                Err(EvaluationArtifactError::SiteDomainMismatch)
            ));
            let mut wrong_actions = decoded_artifact.clone();
            wrong_actions.forward_action_domain.count -= 1;
            assert!(matches!(
                wrong_actions.validate_against("add_sub_lui_auipc_mop", &context, &actions),
                Err(EvaluationArtifactError::ForwardActionDomainMismatch)
            ));
        }
        let compiled = compile_layer_with_evaluation_genome(
            "add_sub_lui_auipc_mop",
            layer,
            artifact_layer,
            &artifact.scratch_space_mapping,
            &cross,
            BUDGET_CELLS,
            &decoded_artifact,
        )
        .unwrap_or_else(|error| panic!("compile add_sub layer {layer_index}: {error:?}"));
        assert_eq!(compiled.root_order, scored.root_order);
        assert_eq!(compiled.fitness, scored.fitness);
        layer_artifacts.push(decoded_artifact);
        let concrete = compiled.concrete;

        assert_eq!(
            concrete.compiled.stats.dram_traffic, packed.stats.dram_read_lanes,
            "layer {layer_index} predicted and concrete read traffic",
        );
        assert_eq!(
            scored.fitness.program_instructions, concrete.compiled.stats.program_lanes,
            "layer {layer_index} search/final instruction certificate",
        );
        assert_eq!(
            scored.fitness.encoded_lanes, concrete.stats.encoded_lanes,
            "layer {layer_index} search/final encoding certificate",
        );
        assert!(
            concrete.stats.max_live_lanes <= BUDGET_LANES,
            "layer {layer_index} concrete placement respects the lane budget",
        );
        let concrete_roots = concrete
            .compiled
            .root_outputs
            .iter()
            .map(|(root, _)| *root)
            .collect::<std::collections::HashSet<_>>();
        let expected_roots = actions
            .iter()
            .filter_map(|(&root, action)| {
                (!matches!(action, ForwardAction::SkipScratchPrefill)).then_some(root)
            })
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(
            concrete_roots, expected_roots,
            "layer {layer_index} forward action root set",
        );

        for row in common::sample_rows(dag.globals.trace_len) {
            assert_eq!(
                interpret_packed_plan(&packed, layer, row, &resolvers)
                    .expect("interpret packed plan"),
                interpret_plan(plan, layer, row, &resolvers).expect("interpret symbolic plan"),
                "layer {layer_index} symbolic/packed parity at row {row}",
            );
            let outputs = interpret_layer_row(&concrete.compiled, layer, &resolvers, row)
                .expect("interpret concrete program");
            for &(root, _) in &concrete.compiled.root_outputs {
                assert_eq!(
                    outputs.by_root[&root],
                    gkr_eval_ir::eval_layer_root(layer, root, row, &resolvers),
                    "layer {layer_index} canonical root parity for root {} at row {row}",
                    root.0,
                );
            }
        }
    }
    assert!(
        exercised_nonzero_layer,
        "smoke fixture must exercise explicit nonzero-layer certification",
    );

    let circuit_artifact = EvaluationGenomeCircuitArtifact::new(
        "add_sub_lui_auipc_mop",
        EvaluationLayoutVariant::WithCaches,
        ADD_SUB,
        BUDGET_CELLS,
        SearchProvenance {
            algorithm: "retentive-smoke".to_owned(),
            seed: 0,
            evaluations: 0,
            staging_evaluations: 0,
        },
        layer_artifacts,
    )
    .expect("build add_sub circuit artifact");
    let circuit_json =
        serde_json::to_string(&circuit_artifact).expect("serialize circuit artifact");
    let decoded_circuit: EvaluationGenomeCircuitArtifact =
        serde_json::from_str(&circuit_json).expect("deserialize circuit artifact");
    assert_eq!(decoded_circuit, circuit_artifact);
    let committed_path = common::compiled_circuit_dir().join(ADD_SUB_EVAL_PLAN);
    let committed = load_evaluation_genome_artifact(&committed_path)
        .unwrap_or_else(|error| panic!("load {}: {error:?}", committed_path.display()));
    assert_eq!(committed.layers.len(), circuit_artifact.layers.len());
    for (layer, (committed, retentive)) in committed
        .layers
        .iter()
        .zip(&circuit_artifact.layers)
        .enumerate()
    {
        assert!(
            committed.expected_fitness <= retentive.expected_fitness,
            "committed layer {layer} regressed below retentive baseline: {:?} > {:?}",
            committed.expected_fitness,
            retentive.expected_fitness,
        );
    }
    assert!(matches!(
        compile_circuit_with_evaluation_genomes(
            &dag,
            &artifact,
            "add_sub_lui_auipc_mop",
            "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
            EvaluationLayoutVariant::NoCaches,
            &committed,
        ),
        Err(EvaluationCompileError::LayoutFixtureMismatch { .. })
    ));
    assert!(matches!(
        compile_circuit_with_evaluation_genomes(
            &dag,
            &artifact,
            "add_sub_lui_auipc_mop",
            ADD_SUB,
            EvaluationLayoutVariant::NoCaches,
            &committed,
        ),
        Err(EvaluationCompileError::LayoutVariantMismatch { .. })
    ));
    let mut tampered_fitness = committed.clone();
    tampered_fitness.layers[0]
        .expected_fitness
        .program_instructions += 1;
    tampered_fitness.expected_fitness.program_instructions += 1;
    assert!(matches!(
        compile_circuit_with_evaluation_genomes(
            &dag,
            &artifact,
            "add_sub_lui_auipc_mop",
            ADD_SUB,
            EvaluationLayoutVariant::WithCaches,
            &tampered_fitness,
        ),
        Err(EvaluationCompileError::FitnessCertificateMismatch { .. })
    ));
    let compiled_circuit = compile_circuit_with_evaluation_genomes(
        &dag,
        &artifact,
        "add_sub_lui_auipc_mop",
        ADD_SUB,
        EvaluationLayoutVariant::WithCaches,
        &committed,
    )
    .expect("compile add_sub whole-circuit evaluation artifact");
    assert_eq!(compiled_circuit.layers.len(), dag.layers.len());
    assert_eq!(compiled_circuit.fitness, committed.expected_fitness);
    let established_schedule =
        load_committed_schedule(&common::schedule_path("add_sub_lui_auipc_mop"))
            .expect("load established add_sub b16 schedule");
    let established = compile_circuit(&dag, &established_schedule, &artifact)
        .expect("compile established add_sub b16 program");
    for (layer, (searched, established)) in compiled_circuit
        .layers
        .iter()
        .zip(&established.layers)
        .enumerate()
    {
        assert!(
            searched.fitness.dram_read_lanes <= established.stats.dram_traffic,
            "searched layer {layer} read regression: {} > {}",
            searched.fitness.dram_read_lanes,
            established.stats.dram_traffic,
        );
    }
    let established_instructions = established
        .layers
        .iter()
        .map(|layer| layer.stats.program_lanes)
        .sum::<usize>();
    assert!(
        compiled_circuit.fitness.program_instructions <= established_instructions,
        "searched add_sub instruction regression: {} > {established_instructions}",
        compiled_circuit.fitness.program_instructions,
    );
    let incumbent_preserved = produce_searched_evaluation_genome_artifact(
        &dag,
        &artifact,
        "add_sub_lui_auipc_mop",
        ADD_SUB,
        EvaluationLayoutVariant::WithCaches,
        BUDGET_CELLS,
        MutationSearchConfig {
            population: 2,
            evaluations: 2,
            staging_evaluations: 0,
            seed: 1,
            cache_mutations: 1,
        },
        Some(&committed),
    )
    .expect("preserve searched incumbent during bounded regeneration");
    assert_eq!(
        incumbent_preserved.expected_fitness,
        committed.expected_fitness
    );
    assert!(
        incumbent_preserved
            .layers
            .iter()
            .zip(&committed.layers)
            .all(|(produced, incumbent)| produced.genome == incumbent.genome),
        "a non-improving bounded search must retain every incumbent layer",
    );
    for (layer_index, (dag_layer, compiled_layer)) in
        dag.layers.iter().zip(&compiled_circuit.layers).enumerate()
    {
        for row in common::sample_rows(dag.globals.trace_len) {
            let outputs = interpret_layer_row(
                &compiled_layer.concrete.compiled,
                dag_layer,
                &resolvers,
                row,
            )
            .unwrap_or_else(|error| {
                panic!("interpret searched layer {layer_index} row {row}: {error:?}")
            });
            for &(root, _) in &compiled_layer.concrete.compiled.root_outputs {
                assert_eq!(
                    outputs.by_root[&root],
                    gkr_eval_ir::eval_layer_root(dag_layer, root, row, &resolvers,),
                    "searched layer {layer_index} root {} row {row}",
                    root.0,
                );
            }
        }
    }
}

#[test]
fn forward_with_caches_c4_artifact_corpus_compiles_and_matches_values() {
    let synthetic = common::SyntheticResolvers;
    let resolvers = common::resolvers(&synthetic);
    let mut searched_reads = 0usize;
    let mut established_reads = 0usize;
    let mut searched_instructions = 0usize;
    let mut established_instructions = 0usize;

    for &(circuit, fixture) in FORWARD_CORPUS {
        let layout = common::load_fixture(fixture);
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower {fixture}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("validate {fixture}: {error}"));
        let path = evaluation_artifact_path(circuit);
        let artifact = load_evaluation_genome_artifact(&path)
            .unwrap_or_else(|error| panic!("load {}: {error:?}", path.display()));
        assert_eq!(
            artifact.budget_cells, 4,
            "{circuit}: loaded c4 artifact budget"
        );
        let searched = compile_circuit_with_evaluation_genomes(
            &dag,
            &layout,
            circuit,
            fixture,
            EvaluationLayoutVariant::WithCaches,
            &artifact,
        )
        .unwrap_or_else(|error| panic!("compile searched {circuit}: {error:?}"));
        assert_eq!(
            searched.budget_cells, 4,
            "{circuit}: compiled c4 artifact budget"
        );
        let schedule = load_committed_schedule(&common::schedule_path(circuit))
            .unwrap_or_else(|error| panic!("load established {circuit}: {error:?}"));
        let established = compile_circuit(&dag, &schedule, &layout)
            .unwrap_or_else(|error| panic!("compile established {circuit}: {error:?}"));

        for (layer_index, ((dag_layer, searched_layer), established_layer)) in dag
            .layers
            .iter()
            .zip(&searched.layers)
            .zip(&established.layers)
            .enumerate()
        {
            assert!(
                searched_layer.fitness.dram_read_lanes <= established_layer.stats.dram_traffic,
                "{circuit} layer {layer_index} read regression: {} > {}",
                searched_layer.fitness.dram_read_lanes,
                established_layer.stats.dram_traffic,
            );
            for row in common::sample_rows(dag.globals.trace_len) {
                let outputs = interpret_layer_row(
                    &searched_layer.concrete.compiled,
                    dag_layer,
                    &resolvers,
                    row,
                )
                .unwrap_or_else(|error| {
                    panic!("interpret {circuit} layer {layer_index} row {row}: {error:?}")
                });
                for &(root, _) in &searched_layer.concrete.compiled.root_outputs {
                    assert_eq!(
                        outputs.by_root[&root],
                        gkr_eval_ir::eval_layer_root(dag_layer, root, row, &resolvers,),
                        "{circuit} layer {layer_index} root {} row {row}",
                        root.0,
                    );
                }
            }
        }
        searched_reads += searched.fitness.dram_read_lanes;
        searched_instructions += searched.fitness.program_instructions;
        established_reads += established
            .layers
            .iter()
            .map(|layer| layer.stats.dram_traffic)
            .sum::<usize>();
        established_instructions += established
            .layers
            .iter()
            .map(|layer| layer.stats.program_lanes)
            .sum::<usize>();
    }

    assert!(searched_reads <= established_reads);
    assert!(searched_instructions <= established_instructions);
}

#[test]
#[ignore = "on-demand golden regen: set GKR_PRODUCE_EVAL_PLAN_ARTIFACT=1"]
fn produce_add_sub_searched_evaluation_artifact() {
    if std::env::var("GKR_PRODUCE_EVAL_PLAN_ARTIFACT").is_err() || std::env::var("CI").is_ok() {
        eprintln!("skipping producer (set GKR_PRODUCE_EVAL_PLAN_ARTIFACT=1, not in CI)");
        return;
    }
    let layout = common::load_fixture(ADD_SUB);
    let dag = lower_dag(&layout).expect("lower add_sub fixture");
    validate(&dag).expect("validate add_sub DAG");
    let path = common::compiled_circuit_dir().join(ADD_SUB_EVAL_PLAN);
    let incumbent = load_evaluation_genome_artifact(&path).ok();
    let evaluations = std::env::var("EVAL_PLAN_EVALUATIONS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(128);
    let staging_evaluations = std::env::var("EVAL_PLAN_STAGING_EVALUATIONS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(64);
    let artifact = produce_searched_evaluation_genome_artifact(
        &dag,
        &layout,
        "add_sub_lui_auipc_mop",
        ADD_SUB,
        EvaluationLayoutVariant::WithCaches,
        4,
        MutationSearchConfig {
            population: 16,
            evaluations,
            staging_evaluations,
            seed: 0,
            cache_mutations: 2,
        },
        incumbent.as_ref(),
    )
    .expect("produce searched add_sub artifact");
    if incumbent
        .as_ref()
        .is_some_and(|incumbent| artifact.expected_fitness >= incumbent.expected_fitness)
    {
        eprintln!(
            "kept {} ({:?} >= incumbent {:?})",
            path.display(),
            artifact.expected_fitness,
            incumbent.as_ref().unwrap().expected_fitness,
        );
        return;
    }
    let temporary = path.with_extension("json.tmp");
    let mut file = std::fs::File::create(&temporary)
        .unwrap_or_else(|error| panic!("create {}: {error}", temporary.display()));
    serde_json::to_writer_pretty(&mut file, &artifact)
        .unwrap_or_else(|error| panic!("write {}: {error}", temporary.display()));
    file.sync_all()
        .unwrap_or_else(|error| panic!("sync {}: {error}", temporary.display()));
    std::fs::rename(&temporary, &path).unwrap_or_else(|error| {
        panic!(
            "rename {} to {}: {error}",
            temporary.display(),
            path.display()
        )
    });
    eprintln!("wrote {}", path.display());
}

#[test]
#[ignore = "on-demand corpus regen: set GKR_PRODUCE_EVAL_PLAN_CORPUS=1"]
fn produce_forward_with_caches_c4_evaluation_artifact_corpus() {
    if std::env::var("GKR_PRODUCE_EVAL_PLAN_CORPUS").is_err() || std::env::var("CI").is_ok() {
        eprintln!("skipping producer (set GKR_PRODUCE_EVAL_PLAN_CORPUS=1, not in CI)");
        return;
    }
    let evaluations = std::env::var("EVAL_PLAN_EVALUATIONS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(128);
    let staging_evaluations = std::env::var("EVAL_PLAN_STAGING_EVALUATIONS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(64);
    let config = MutationSearchConfig {
        population: 16,
        evaluations,
        staging_evaluations,
        seed: 0,
        cache_mutations: 2,
    };
    let mut pending = Vec::with_capacity(FORWARD_CORPUS.len());
    let mut searched_reads = 0usize;
    let mut established_reads = 0usize;
    let mut searched_instructions = 0usize;
    let mut established_instructions = 0usize;

    for &(circuit, fixture) in FORWARD_CORPUS {
        let layout = common::load_fixture(fixture);
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower {fixture}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("validate {fixture}: {error}"));
        let path = evaluation_artifact_path(circuit);
        let incumbent = path.exists().then(|| {
            load_evaluation_genome_artifact(&path)
                .unwrap_or_else(|error| panic!("load incumbent {}: {error:?}", path.display()))
        });
        let artifact = produce_searched_evaluation_genome_artifact(
            &dag,
            &layout,
            circuit,
            fixture,
            EvaluationLayoutVariant::WithCaches,
            4,
            config,
            incumbent.as_ref(),
        )
        .unwrap_or_else(|error| panic!("search {circuit}: {error:?}"));
        let searched = compile_circuit_with_evaluation_genomes(
            &dag,
            &layout,
            circuit,
            fixture,
            EvaluationLayoutVariant::WithCaches,
            &artifact,
        )
        .unwrap_or_else(|error| panic!("compile searched {circuit}: {error:?}"));
        let schedule = load_committed_schedule(&common::schedule_path(circuit))
            .unwrap_or_else(|error| panic!("load established {circuit}: {error:?}"));
        let established = compile_circuit(&dag, &schedule, &layout)
            .unwrap_or_else(|error| panic!("compile established {circuit}: {error:?}"));
        for (layer, (searched_layer, established_layer)) in
            searched.layers.iter().zip(&established.layers).enumerate()
        {
            assert!(
                searched_layer.fitness.dram_read_lanes <= established_layer.stats.dram_traffic,
                "{circuit} layer {layer} read regression: {} > {}",
                searched_layer.fitness.dram_read_lanes,
                established_layer.stats.dram_traffic,
            );
        }
        let old_reads = established
            .layers
            .iter()
            .map(|layer| layer.stats.dram_traffic)
            .sum::<usize>();
        let old_instructions = established
            .layers
            .iter()
            .map(|layer| layer.stats.program_lanes)
            .sum::<usize>();
        searched_reads += searched.fitness.dram_read_lanes;
        established_reads += old_reads;
        searched_instructions += searched.fitness.program_instructions;
        established_instructions += old_instructions;
        eprintln!(
            "artifact_candidate circuit={circuit} reads={}/{} instructions={}/{} fitness={:?}",
            searched.fitness.dram_read_lanes,
            old_reads,
            searched.fitness.program_instructions,
            old_instructions,
            searched.fitness,
        );
        pending.push((path, incumbent, artifact));
    }

    assert!(
        searched_reads <= established_reads,
        "corpus read regression: {searched_reads} > {established_reads}",
    );
    assert!(
        searched_instructions <= established_instructions,
        "corpus instruction regression: {searched_instructions} > {established_instructions}",
    );
    eprintln!(
        "artifact_candidate corpus reads={searched_reads}/{established_reads} \
         instructions={searched_instructions}/{established_instructions}",
    );

    let mut replacements = Vec::new();
    for (path, incumbent, artifact) in pending {
        if incumbent
            .as_ref()
            .is_some_and(|incumbent| artifact.expected_fitness >= incumbent.expected_fitness)
        {
            eprintln!("kept {}", path.display());
            continue;
        }
        let temporary = path.with_extension("json.tmp");
        let mut file = std::fs::File::create(&temporary)
            .unwrap_or_else(|error| panic!("create {}: {error}", temporary.display()));
        serde_json::to_writer_pretty(&mut file, &artifact)
            .unwrap_or_else(|error| panic!("write {}: {error}", temporary.display()));
        file.sync_all()
            .unwrap_or_else(|error| panic!("sync {}: {error}", temporary.display()));
        replacements.push((temporary, path));
    }
    for (temporary, path) in replacements {
        std::fs::rename(&temporary, &path).unwrap_or_else(|error| {
            panic!(
                "rename {} to {}: {error}",
                temporary.display(),
                path.display()
            )
        });
        eprintln!("wrote {}", path.display());
    }
}

#[test]
#[ignore = "on-demand persisted-artifact size census"]
fn measure_retentive_evaluation_artifact_sizes() {
    let mut total = 0usize;
    for &(circuit, fixture) in FORWARD_CORPUS {
        let layout = common::load_fixture(fixture);
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower {fixture}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("validate {fixture}: {error}"));
        let artifact = capture_retentive_circuit_artifact(circuit, fixture, &dag, &layout);
        let bytes = serde_json::to_vec(&artifact)
            .unwrap_or_else(|error| panic!("serialize {fixture}: {error}"));
        total += bytes.len();
        eprintln!("artifact_size circuit={circuit} bytes={}", bytes.len());
    }
    eprintln!("artifact_size total_bytes={total}");
}

#[test]
#[ignore = "on-demand real-layer evaluation-plan search measurement"]
fn search_add_sub_layer_zero() {
    let artifact = common::load_fixture(ADD_SUB);
    let dag = lower_dag(&artifact).expect("lower add_sub fixture");
    validate(&dag).expect("validate add_sub DAG");
    let cross = build_cross_layer_field_map(&dag);
    let layer = &dag.layers[0];
    let fields = (0..layer.exprs.len())
        .map(
            |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                OperandField::Base => FieldKind::Base,
                OperandField::Ext => FieldKind::Ext,
            },
        )
        .collect::<Vec<_>>();

    let actions =
        build_forward_actions(layer, &artifact.layers[0], &artifact.scratch_space_mapping)
            .expect("classify forward roots");
    let compute_roots = actions
        .iter()
        .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
        .collect::<Vec<_>>();
    let committed = load_committed_schedule(&common::schedule_path("add_sub_lui_auipc_mop"))
        .expect("load committed add_sub schedule");
    let synthetic = common::SyntheticResolvers;
    let resolvers = common::resolvers(&synthetic);

    for (budget_cells, expected_reference, expected_committed, expected_new) in
        [(4, 31, 31, 31), (3, 36, 35, 31), (2, 51, 48, 33)]
    {
        let budget_lanes = budget_cells * 4;
        let reference_context =
            LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, budget_lanes);
        let reference_genome = ReferenceGenome::neutral(
            reference_context.n_order_keys(),
            reference_context.n_sites(),
        );
        let reference = score_reference(&reference_genome, &reference_context);
        let committed_genome = genome_from_schedule(&committed.layers[0], &reference_context);
        let committed_score = score_reference(&committed_genome, &reference_context);
        assert_eq!(reference.dram_traffic, expected_reference);
        assert_eq!(committed_score.dram_traffic, expected_committed);

        let build_started = Instant::now();
        let context = PlanSearchContext::build_for_roots(
            layer,
            &fields,
            artifact.layers[0].layer,
            budget_cells,
            &compute_roots,
        )
        .expect("build search context");
        let build_elapsed = build_started.elapsed();
        let neutral = context
            .score(&EvaluationGenome::neutral(&context))
            .expect("score neutral plan");
        let retentive = context
            .score(&EvaluationGenome::retentive(&context))
            .expect("score retentive plan");
        let search_started = Instant::now();
        let (best, evaluations) = if budget_lanes == 16 || budget_lanes == 8 {
            let outcome = mutation_search(
                &context,
                MutationSearchConfig {
                    population: if budget_lanes == 8 { 16 } else { 4 },
                    evaluations: if budget_lanes == 8 { 512 } else { 8 },
                    staging_evaluations: 0,
                    seed: 0,
                    cache_mutations: 2,
                },
            )
            .expect("search add_sub layer zero");
            (outcome.best, outcome.evaluations)
        } else if retentive.fitness < neutral.fitness {
            (retentive.clone(), 2)
        } else {
            (neutral.clone(), 2)
        };
        let search_elapsed = search_started.elapsed();
        let neutral_plan = neutral
            .plan
            .as_ref()
            .expect("neutral plan must be feasible");
        let best_plan = best.plan.as_ref().expect("winning plan must be feasible");
        if budget_lanes == 16 {
            assert_eq!(reference.dram_traffic, reference_context.floor);
        }
        if budget_lanes >= 12 {
            assert_eq!(best.fitness.dram_read_lanes, reference_context.floor);
        }
        assert_eq!(best.fitness.dram_read_lanes, expected_new);
        assert!(best.fitness.dram_read_lanes <= committed_score.dram_traffic);

        let neutral_packed = pack_plan(neutral_plan, layer, PackConfig::default()).unwrap();
        let best_packed = pack_plan(best_plan, layer, PackConfig::default()).unwrap();
        let neutral_concrete = bind_packed_plan(
            &neutral_packed,
            layer,
            context.materialized_roots(),
            0,
            budget_lanes,
        )
        .unwrap();
        let best_concrete = bind_packed_plan(
            &best_packed,
            layer,
            context.materialized_roots(),
            0,
            budget_lanes,
        )
        .unwrap();
        assert_eq!(
            interpret_packed_plan(&best_packed, layer, 0, &resolvers).unwrap(),
            interpret_plan(best_plan, layer, 0, &resolvers).unwrap()
        );
        let concrete_outputs =
            interpret_layer_row(&best_concrete.compiled, layer, &resolvers, 0).unwrap();
        for &root in context.materialized_roots() {
            assert_eq!(
                concrete_outputs.by_root[&root],
                gkr_eval_ir::eval_layer_root(layer, root, 0, &resolvers),
            );
        }
        assert_eq!(
            neutral_concrete.compiled.stats.program_lanes,
            neutral_packed.stats.packed_instructions,
        );
        assert_eq!(
            best_concrete.compiled.stats.dram_traffic,
            best_packed.stats.dram_read_lanes,
        );

        println!(
            "eval-plan add_sub L0: budget={} exprs={} units={} sites={} floor={} reference={} committed={} \
             neutral={} retentive={} best={} overhead(ref/committed/new)={}/{}/{} arithmetic={}->{} \
             instructions={}->{} (neutral), {}->{} (best) encoded_lanes={}->{} evals={} build={:?} search={:?}",
            budget_lanes,
            layer.exprs.len(),
            context.units().len(),
            context.site_index().len(),
            reference_context.floor,
            reference.dram_traffic,
            committed_score.dram_traffic,
            neutral.fitness.dram_read_lanes,
            retentive.fitness.dram_read_lanes,
            best.fitness.dram_read_lanes,
            reference.dram_traffic - reference_context.floor,
            committed_score.dram_traffic - reference_context.floor,
            best.fitness.dram_read_lanes - reference_context.floor,
            neutral.fitness.arithmetic_ops,
            best.fitness.arithmetic_ops,
            neutral_packed.stats.unpacked_instructions,
            neutral_packed.stats.packed_instructions,
            best_packed.stats.unpacked_instructions,
            best_packed.stats.packed_instructions,
            neutral_packed.stats.encoded_lanes,
            best_packed.stats.encoded_lanes,
            evaluations,
            build_elapsed,
            search_elapsed,
        );
        assert!(best.fitness <= neutral.fitness);
    }
}

#[test]
#[ignore = "on-demand concrete forward-corpus comparison"]
fn compare_forward_corpus_layer_zero() {
    assert_eq!(FORWARD_CORPUS.len(), 11, "scheduled reference corpus drift");
    let budget_cells = std::env::var("EVAL_PLAN_BUDGET")
        .ok()
        .map(|budgets| {
            budgets
                .split(',')
                .map(|budget| budget.parse::<usize>().expect("numeric EVAL_PLAN_BUDGET"))
                .collect::<Vec<_>>()
        })
        .unwrap_or_else(|| vec![4, 3, 2]);
    let circuit_filter = std::env::var("EVAL_PLAN_CIRCUIT").ok();
    let search_evaluations = std::env::var("EVAL_PLAN_EVALUATIONS")
        .ok()
        .map(|evaluations| {
            evaluations
                .parse::<usize>()
                .expect("numeric EVAL_PLAN_EVALUATIONS")
        })
        .unwrap_or(0);
    let synthetic = common::SyntheticResolvers;
    let resolvers = common::resolvers(&synthetic);

    for &(stem, fixture) in FORWARD_CORPUS {
        if circuit_filter
            .as_deref()
            .is_some_and(|filter| filter != stem)
        {
            continue;
        }
        let artifact = common::load_fixture(fixture);
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("lower {stem}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("validate {stem}: {error}"));
        let cross = build_cross_layer_field_map(&dag);
        let layer = &dag.layers[0];
        let fields = (0..layer.exprs.len())
            .map(
                |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                    OperandField::Base => FieldKind::Base,
                    OperandField::Ext => FieldKind::Ext,
                },
            )
            .collect::<Vec<_>>();
        let actions =
            build_forward_actions(layer, &artifact.layers[0], &artifact.scratch_space_mapping)
                .unwrap_or_else(|error| panic!("classify {stem} forward roots: {error:?}"));
        let compute_roots = actions
            .iter()
            .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
            .collect::<Vec<_>>();
        let committed = load_committed_schedule(&common::schedule_path(stem))
            .unwrap_or_else(|error| panic!("load {stem} committed schedule: {error:?}"));

        for &budget_cells in &budget_cells {
            let budget_lanes = budget_cells
                .checked_mul(4)
                .expect("configured cell budget fits lanes");
            let reference_context =
                LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, budget_lanes);
            let reference_genome = ReferenceGenome::neutral(
                reference_context.n_order_keys(),
                reference_context.n_sites(),
            );
            let reference = score_reference(&reference_genome, &reference_context);
            let committed_genome = genome_from_schedule(&committed.layers[0], &reference_context);
            let committed_score = score_reference(&committed_genome, &reference_context);

            let started = Instant::now();
            let context = PlanSearchContext::build_for_roots(
                layer,
                &fields,
                artifact.layers[0].layer,
                budget_cells,
                &compute_roots,
            )
            .unwrap_or_else(|error| panic!("build {stem} b{budget_lanes} context: {error:?}"));
            let neutral = context
                .score(&EvaluationGenome::neutral(&context))
                .unwrap_or_else(|error| panic!("score {stem} b{budget_lanes} neutral: {error:?}"));
            let retentive = context
                .score(&EvaluationGenome::retentive(&context))
                .unwrap_or_else(|error| {
                    panic!("score {stem} b{budget_lanes} retentive: {error:?}")
                });
            let search = (search_evaluations > 0).then(|| {
                mutation_search(
                    &context,
                    MutationSearchConfig {
                        population: 16,
                        evaluations: search_evaluations,
                        staging_evaluations: 0,
                        seed: 0,
                        cache_mutations: 2,
                    },
                )
                .unwrap_or_else(|error| panic!("search {stem} b{budget_lanes}: {error:?}"))
            });
            let baseline_best = if retentive.fitness < neutral.fitness {
                &retentive
            } else {
                &neutral
            };
            let best = search
                .as_ref()
                .map(|outcome| &outcome.best)
                .filter(|candidate| candidate.fitness < baseline_best.fitness)
                .unwrap_or(baseline_best);
            let plan = best.plan.as_ref().unwrap_or_else(|| {
                panic!("{stem} b{budget_lanes} neutral and retentive plans are infeasible")
            });
            let packed = pack_plan(plan, layer, PackConfig::default())
                .unwrap_or_else(|error| panic!("pack {stem} b{budget_lanes}: {error:?}"));
            let concrete = bind_packed_plan(
                &packed,
                layer,
                context.materialized_roots(),
                0,
                budget_lanes,
            )
            .unwrap_or_else(|error| panic!("bind {stem} b{budget_lanes}: {error:?}"));

            assert_eq!(
                interpret_packed_plan(&packed, layer, 0, &resolvers).unwrap(),
                interpret_plan(plan, layer, 0, &resolvers).unwrap(),
                "{stem} b{budget_lanes} packed parity",
            );
            let concrete_outputs =
                interpret_layer_row(&concrete.compiled, layer, &resolvers, 0).unwrap();
            for &root in context.materialized_roots() {
                assert_eq!(
                    concrete_outputs.by_root[&root],
                    gkr_eval_ir::eval_layer_root(layer, root, 0, &resolvers),
                    "{stem} b{budget_lanes} root {}",
                    root.0,
                );
            }
            assert_eq!(
                concrete.compiled.stats.dram_traffic, packed.stats.dram_read_lanes,
                "{stem} b{budget_lanes} traffic prediction",
            );
            println!(
                "eval-plan corpus: circuit={stem} budget={budget_lanes} sites={} floor={} natural={} \
                 committed={} neutral={} retentive={} best={} floor_gap={} moves={} evals={} placement={:?} \
                 elapsed={:?}",
                context.site_index().len(),
                reference_context.floor,
                reference.dram_traffic,
                committed_score.dram_traffic,
                neutral.fitness.dram_read_lanes,
                retentive.fitness.dram_read_lanes,
                best.fitness.dram_read_lanes,
                best.fitness.dram_read_lanes - reference_context.floor,
                concrete.stats.relocation_moves,
                search.as_ref().map_or(2, |outcome| outcome.evaluations),
                search.as_ref().map(|outcome| outcome.telemetry),
                started.elapsed(),
            );
        }
    }
}

#[test]
#[ignore = "on-demand all-layer concrete forward-corpus comparison"]
fn compare_forward_corpus_all_layers() {
    assert_eq!(FORWARD_CORPUS.len(), 11, "scheduled reference corpus drift");
    let circuit_filter = std::env::var("EVAL_PLAN_CIRCUIT").ok();
    let layer_filter = std::env::var("EVAL_PLAN_LAYER")
        .ok()
        .map(|layer| layer.parse::<usize>().expect("numeric EVAL_PLAN_LAYER"));
    let configured_budget_cells = std::env::var("EVAL_PLAN_BUDGET").ok().map(|budgets| {
        budgets
            .split(',')
            .map(|budget| budget.parse::<usize>().expect("numeric EVAL_PLAN_BUDGET"))
            .collect::<Vec<_>>()
    });
    let search_evaluations = std::env::var("EVAL_PLAN_EVALUATIONS")
        .ok()
        .map(|evaluations| {
            evaluations
                .parse::<usize>()
                .expect("numeric EVAL_PLAN_EVALUATIONS")
        })
        .unwrap_or(0);
    let staging_evaluations = std::env::var("EVAL_PLAN_STAGING_EVALUATIONS")
        .ok()
        .map(|evaluations| {
            evaluations
                .parse::<usize>()
                .expect("numeric EVAL_PLAN_STAGING_EVALUATIONS")
        })
        .unwrap_or(0);
    let report_attribution = std::env::var_os("EVAL_PLAN_ATTRIBUTION").is_some();
    let controlled_diff = std::env::var_os("EVAL_PLAN_CONTROLLED_DIFF").is_some();
    let synthetic = common::SyntheticResolvers;
    let resolvers = common::resolvers(&synthetic);

    for &(stem, fixture) in FORWARD_CORPUS {
        if circuit_filter
            .as_deref()
            .is_some_and(|filter| filter != stem)
        {
            continue;
        }
        let artifact = common::load_fixture(fixture);
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("lower {stem}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("validate {stem}: {error}"));
        let cross = build_cross_layer_field_map(&dag);
        let committed = load_committed_schedule(&common::schedule_path(stem))
            .unwrap_or_else(|error| panic!("load {stem} committed schedule: {error:?}"));
        let budget_cells = configured_budget_cells
            .clone()
            .unwrap_or_else(|| vec![4, 3, 2]);
        let established_by_cells = budget_cells
            .iter()
            .map(|&budget_cells| {
                let budget_lanes = budget_cells
                    .checked_mul(4)
                    .expect("configured cell budget fits lanes");
                let mut schedule = committed.clone();
                schedule.budget = budget_lanes;
                let compiled =
                    compile_circuit(&dag, &schedule, &artifact).unwrap_or_else(|error| {
                        panic!("compile established {stem} b{budget_lanes}: {error:?}")
                    });
                (budget_cells, compiled)
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            artifact.layers.len(),
            dag.layers.len(),
            "{stem} artifact/DAG layers"
        );
        assert_eq!(
            committed.layers.len(),
            dag.layers.len(),
            "{stem} schedule/DAG layers"
        );
        for (&budget_cells, established) in &established_by_cells {
            assert_eq!(
                established.layers.len(),
                dag.layers.len(),
                "{stem} c{budget_cells} compiled/DAG layers"
            );
        }

        for (layer_index, layer) in dag.layers.iter().enumerate() {
            if layer_filter.is_some_and(|filter| filter != layer_index) {
                continue;
            }
            let artifact_layer = &artifact.layers[layer_index];
            let actions =
                build_forward_actions(layer, artifact_layer, &artifact.scratch_space_mapping)
                    .unwrap_or_else(|error| {
                        panic!("classify {stem} layer {layer_index}: {error:?}")
                    });
            let compute_roots = actions
                .iter()
                .filter_map(|(&root, action)| {
                    matches!(action, ForwardAction::Compute).then_some(root)
                })
                .collect::<Vec<_>>();
            let alias_roots = actions
                .values()
                .filter(|action| matches!(action, ForwardAction::CopyAlias { .. }))
                .count();
            let skipped_roots = actions
                .values()
                .filter(|action| matches!(action, ForwardAction::SkipScratchPrefill))
                .count();
            if compute_roots.is_empty() {
                println!(
                    "eval-plan all-layers: circuit={stem} layer={layer_index} \
                     artifact_layer={} compute_roots=0 aliases={alias_roots} skipped={skipped_roots}",
                    artifact_layer.layer,
                );
                continue;
            }
            let fields = (0..layer.exprs.len())
                .map(
                    |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                        OperandField::Base => FieldKind::Base,
                        OperandField::Ext => FieldKind::Ext,
                    },
                )
                .collect::<Vec<_>>();

            for &budget_cells in &budget_cells {
                let budget_lanes = budget_cells
                    .checked_mul(4)
                    .expect("configured cell budget fits lanes");
                let started = Instant::now();
                let established = &established_by_cells[&budget_cells];
                let reference_context =
                    LayerCtx::new(layer, artifact_layer, &artifact, &cross, budget_lanes);
                let reference = score_reference(
                    &ReferenceGenome::neutral(
                        reference_context.n_order_keys(),
                        reference_context.n_sites(),
                    ),
                    &reference_context,
                );
                let committed_score = score_reference(
                    &genome_from_schedule(&committed.layers[layer_index], &reference_context),
                    &reference_context,
                );
                let context = PlanSearchContext::build_for_roots(
                    layer,
                    &fields,
                    artifact_layer.layer,
                    budget_cells,
                    &compute_roots,
                )
                .unwrap_or_else(|error| {
                    panic!("build {stem} layer {layer_index} b{budget_lanes}: {error:?}")
                });
                let neutral_genome = EvaluationGenome::neutral(&context);
                let retentive_genome = EvaluationGenome::retentive(&context);
                let neutral = context.score(&neutral_genome).unwrap_or_else(|error| {
                    panic!("score {stem} layer {layer_index} b{budget_lanes} neutral: {error:?}")
                });
                let retentive = context.score(&retentive_genome).unwrap_or_else(|error| {
                    panic!("score {stem} layer {layer_index} b{budget_lanes} retentive: {error:?}")
                });
                let search = (search_evaluations > 0 || staging_evaluations > 0).then(|| {
                    mutation_search(
                        &context,
                        MutationSearchConfig {
                            population: 16,
                            evaluations: search_evaluations.max(2),
                            staging_evaluations,
                            seed: 0,
                            cache_mutations: 2,
                        },
                    )
                    .unwrap_or_else(|error| {
                        panic!("search {stem} layer {layer_index} b{budget_lanes}: {error:?}")
                    })
                });
                let (baseline_best, baseline_genome) = if retentive.fitness < neutral.fitness {
                    (&retentive, &retentive_genome)
                } else {
                    (&neutral, &neutral_genome)
                };
                let best = search
                    .as_ref()
                    .map(|outcome| &outcome.best)
                    .filter(|candidate| candidate.fitness < baseline_best.fitness)
                    .unwrap_or(baseline_best);
                if let Some(outcome) = search
                    .as_ref()
                    .filter(|outcome| outcome.telemetry.staging_evaluations != 0)
                {
                    println!(
                        "eval-plan staging-refinement: circuit={stem} layer={layer_index} \
                         budget={budget_lanes} pairs={} evals={} improvements={} selected={:?}",
                        context.site_index().staging_pairs().len(),
                        outcome.telemetry.staging_evaluations,
                        outcome.telemetry.staging_improvements,
                        outcome.best.fitness,
                    );
                }
                if controlled_diff {
                    let selected_genome = search
                        .as_ref()
                        .filter(|outcome| outcome.best.fitness < baseline_best.fitness)
                        .map(|outcome| &outcome.best_genome)
                        .unwrap_or(baseline_genome);
                    let mut committed_order = selected_genome.clone();
                    committed_order.root_order_key =
                        committed_order_keys(&context, &committed.layers[layer_index]);
                    let committed_order_score = context.score(&committed_order).unwrap_or_else(|error| {
                        panic!("score {stem} layer {layer_index} b{budget_lanes} committed-order ablation: {error:?}")
                    });
                    let compatible = compatible_genome_from_schedule(
                        &context,
                        layer,
                        &committed.layers[layer_index],
                    );
                    let compatible_score = context.score(&compatible).unwrap_or_else(|error| {
                        panic!("score {stem} layer {layer_index} b{budget_lanes} compatible schedule: {error:?}")
                    });
                    let mut exact_root_order = committed.layers[layer_index]
                        .atom_order()
                        .into_iter()
                        .filter(|root| matches!(actions.get(root), Some(ForwardAction::Compute)))
                        .collect::<Vec<_>>();
                    for &root in &best.root_order {
                        if !exact_root_order.contains(&root) {
                            exact_root_order.push(root);
                        }
                    }
                    let mut exact_oracle = GenomeOracle::new(
                        context.site_index(),
                        &selected_genome.cache_priority,
                        &selected_genome.staging_priority,
                    )
                    .expect("exact-order genome oracle");
                    let exact_plan = elaborate_with_oracle_and_sinks(
                        layer,
                        &fields,
                        &exact_root_order,
                        context.materialized_roots(),
                        budget_lanes,
                        &mut exact_oracle,
                    )
                    .expect("elaborate exact committed root order");
                    assert_eq!(exact_oracle.active_site_count(), 0);
                    let exact_packed = pack_plan(&exact_plan, layer, PackConfig::default())
                        .expect("pack exact committed root order");
                    let exact_concrete = bind_packed_plan_with_actions(
                        &exact_packed,
                        layer,
                        context.materialized_roots(),
                        artifact_layer.layer,
                        budget_lanes,
                        &actions,
                        &cross,
                    )
                    .expect("bind exact committed root order");
                    println!(
                        "eval-plan controlled-diff: circuit={stem} layer={layer_index} budget={budget_lanes} \
                         winner={:?} winner_cache_committed_order={:?} compatible_schedule={:?} \
                         exact_root_order=({},{},{}) established_reads={} established_instr={} \
                         retentive_placement={:?} retentive_telemetry={:?}",
                        best.fitness,
                        committed_order_score.fitness,
                        compatible_score.fitness,
                        exact_concrete.compiled.stats.dram_traffic,
                        exact_concrete.compiled.stats.program_lanes,
                        exact_packed.stats.scalar_arithmetic_ops,
                        established.layers[layer_index].stats.dram_traffic,
                        established.layers[layer_index].stats.program_lanes,
                        retentive.placement,
                        retentive.placement_telemetry,
                    );
                    if std::env::var_os("EVAL_PLAN_DISASSEMBLE").is_some() {
                        let controlled_plan = committed_order_score
                            .plan
                            .as_ref()
                            .expect("committed-order plan");
                        let controlled_packed =
                            pack_plan(controlled_plan, layer, PackConfig::default())
                                .expect("pack committed-order plan");
                        let controlled_concrete = bind_packed_plan_with_actions(
                            &controlled_packed,
                            layer,
                            context.materialized_roots(),
                            artifact_layer.layer,
                            budget_lanes,
                            &actions,
                            &cross,
                        )
                        .expect("bind committed-order plan");
                        report_root_segment_diff(
                            layer,
                            &established.layers[layer_index],
                            &controlled_concrete.compiled,
                        );
                        println!(
                            "{}",
                            disassemble_layer(
                                "eval-plan-committed-order",
                                &controlled_concrete.compiled,
                                None,
                            )
                        );
                        println!(
                            "{}",
                            disassemble_layer(
                                "eval-plan-exact-root-order",
                                &exact_concrete.compiled,
                                None,
                            )
                        );
                    }
                    if stem == "add_sub_lui_auipc_mop" && layer_index == 0 && budget_lanes == 16 {
                        report_expr_cone(layer, gkr_eval_ir::RootId(2));
                        report_expr_cone(layer, gkr_eval_ir::RootId(3));
                        report_expr(layer, ExprId(191), "expr-191");
                        report_expr(layer, ExprId(210), "expr-210");
                    }
                }
                let plan = best.plan.as_ref().unwrap_or_else(|| {
                    panic!(
                        "{stem} layer {layer_index} b{budget_lanes} neutral and retentive plans infeasible"
                    )
                });
                if report_attribution {
                    report_plan_attribution(stem, layer_index, budget_lanes, layer, plan);
                }
                let packed =
                    pack_plan(plan, layer, PackConfig::default()).unwrap_or_else(|error| {
                        panic!("pack {stem} layer {layer_index} b{budget_lanes}: {error:?}")
                    });
                let concrete = bind_packed_plan_with_actions(
                    &packed,
                    layer,
                    context.materialized_roots(),
                    artifact_layer.layer,
                    budget_lanes,
                    &actions,
                    &cross,
                )
                .unwrap_or_else(|error| {
                    panic!("bind {stem} layer {layer_index} b{budget_lanes}: {error:?}")
                });
                validate_compiled(&concrete.compiled, layer).unwrap_or_else(|error| {
                    panic!("validate {stem} layer {layer_index} b{budget_lanes}: {error:?}")
                });
                if std::env::var_os("EVAL_PLAN_DISASSEMBLE").is_some() {
                    println!(
                        "{}",
                        disassemble_layer(
                            "established",
                            &established.layers[layer_index],
                            Some(layer),
                        )
                    );
                    println!(
                        "{}",
                        disassemble_layer("eval-plan", &concrete.compiled, None)
                    );
                }
                assert_eq!(
                    concrete.compiled.stats.dram_traffic, packed.stats.dram_read_lanes,
                    "{stem} layer {layer_index} b{budget_lanes} traffic prediction",
                );
                let new_roots = concrete
                    .compiled
                    .root_outputs
                    .iter()
                    .map(|(root, _)| *root)
                    .collect::<std::collections::HashSet<_>>();
                assert_eq!(
                    new_roots,
                    actions
                        .iter()
                        .filter_map(|(&root, action)| {
                            (!matches!(action, ForwardAction::SkipScratchPrefill)).then_some(root)
                        })
                        .collect(),
                    "{stem} layer {layer_index} b{budget_lanes} concrete root set",
                );
                assert_eq!(
                    concrete
                        .compiled
                        .skipped
                        .iter()
                        .copied()
                        .collect::<std::collections::HashSet<_>>(),
                    actions
                        .iter()
                        .filter_map(|(&root, action)| {
                            matches!(action, ForwardAction::SkipScratchPrefill).then_some(root)
                        })
                        .collect(),
                    "{stem} layer {layer_index} b{budget_lanes} skipped root set",
                );

                for row in common::sample_rows(dag.globals.trace_len) {
                    assert_eq!(
                        interpret_packed_plan(&packed, layer, row, &resolvers).unwrap(),
                        interpret_plan(plan, layer, row, &resolvers).unwrap(),
                        "{stem} layer {layer_index} b{budget_lanes} row {row} packed parity",
                    );
                    let new_outputs =
                        interpret_layer_row(&concrete.compiled, layer, &resolvers, row).unwrap();
                    let established_outputs = interpret_layer_row(
                        &established.layers[layer_index],
                        layer,
                        &resolvers,
                        row,
                    )
                    .unwrap();
                    for &(root, _) in &concrete.compiled.root_outputs {
                        let canonical = gkr_eval_ir::eval_layer_root(layer, root, row, &resolvers);
                        assert_eq!(
                            new_outputs.by_root[&root], canonical,
                            "{stem} layer {layer_index} b{budget_lanes} root {} row {row} canonical parity",
                            root.0,
                        );
                        assert_eq!(
                            new_outputs.by_root[&root], established_outputs.by_root[&root],
                            "{stem} layer {layer_index} b{budget_lanes} root {} row {row} established parity",
                            root.0,
                        );
                    }
                }

                let established_arities =
                    arithmetic_arities(&established.layers[layer_index].program);
                let new_arities = arithmetic_arities(&concrete.compiled.program);
                let established_scalar_ops =
                    scalar_isa_ops(&established.layers[layer_index].program);
                let new_scalar_ops = scalar_isa_ops(&concrete.compiled.program);
                println!(
                    "eval-plan all-layers: circuit={stem} layer={layer_index} \
                     artifact_layer={} budget={budget_lanes} roots={} aliases={alias_roots} \
                     skipped={skipped_roots} floor={} natural={} committed={} established={} \
                     neutral={} retentive={} best={} established_instr={} new_instr={} \
                     est_mov={} est_add={} est_mul={} est_fma={} \
                     new_mov={} new_add={} new_mul={} new_fma={} \
                     est_add_args={} est_mul_args={} est_fma_pairs={} \
                     new_add_args={} new_mul_args={} new_fma_pairs={} \
                     est_scalar_ops={} new_scalar_ops={} \
                     encoded={} moves={} evals={} guided={}/{} guided_order={}/{} elapsed={:?}",
                    artifact_layer.layer,
                    context.materialized_roots().len(),
                    reference_context.floor,
                    reference.dram_traffic,
                    committed_score.dram_traffic,
                    established.layers[layer_index].stats.dram_traffic,
                    neutral.fitness.dram_read_lanes,
                    retentive.fitness.dram_read_lanes,
                    best.fitness.dram_read_lanes,
                    established.layers[layer_index].stats.program_lanes,
                    concrete.compiled.stats.program_lanes,
                    established.layers[layer_index].stats.op_counts[0],
                    established.layers[layer_index].stats.op_counts[1],
                    established.layers[layer_index].stats.op_counts[2],
                    established.layers[layer_index].stats.op_counts[3],
                    concrete.compiled.stats.op_counts[0],
                    concrete.compiled.stats.op_counts[1],
                    concrete.compiled.stats.op_counts[2],
                    concrete.compiled.stats.op_counts[3],
                    established_arities[0],
                    established_arities[1],
                    established_arities[2],
                    new_arities[0],
                    new_arities[1],
                    new_arities[2],
                    established_scalar_ops,
                    new_scalar_ops,
                    concrete.stats.encoded_lanes,
                    concrete.stats.relocation_moves,
                    search.as_ref().map_or(2, |outcome| outcome.evaluations),
                    search
                        .as_ref()
                        .map_or(0, |outcome| outcome.telemetry.guided_improvements),
                    search
                        .as_ref()
                        .map_or(0, |outcome| outcome.telemetry.guided_evaluations),
                    search
                        .as_ref()
                        .map_or(0, |outcome| outcome.telemetry.guided_order_improvements),
                    search
                        .as_ref()
                        .map_or(0, |outcome| outcome.telemetry.guided_order_evaluations),
                    started.elapsed(),
                );
            }
        }
    }
}

#[test]
#[ignore = "on-demand established-neutral-semantics ablation"]
fn ablate_first_fit_corpus_budget_3_cells() {
    assert_eq!(FORWARD_CORPUS.len(), 11, "scheduled reference corpus drift");
    let budget_cells = 3;
    let budget_lanes = 12;
    let circuit_filter = std::env::var("EVAL_PLAN_CIRCUIT").ok();

    for &(stem, fixture) in FORWARD_CORPUS {
        if circuit_filter
            .as_deref()
            .is_some_and(|filter| filter != stem)
        {
            continue;
        }
        let started = Instant::now();
        let artifact = common::load_fixture(fixture);
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("lower {stem}: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("validate {stem}: {error}"));
        let cross = build_cross_layer_field_map(&dag);
        let layer = &dag.layers[0];
        let fields = (0..layer.exprs.len())
            .map(
                |index| match expr_operand_field(layer, ExprId(index as u32), &cross) {
                    OperandField::Base => FieldKind::Base,
                    OperandField::Ext => FieldKind::Ext,
                },
            )
            .collect::<Vec<_>>();
        let actions =
            build_forward_actions(layer, &artifact.layers[0], &artifact.scratch_space_mapping)
                .unwrap_or_else(|error| panic!("classify {stem} forward roots: {error:?}"));
        let compute_roots = actions
            .iter()
            .filter_map(|(&root, action)| matches!(action, ForwardAction::Compute).then_some(root))
            .collect::<Vec<_>>();
        let committed = load_committed_schedule(&common::schedule_path(stem))
            .unwrap_or_else(|error| panic!("load {stem} committed schedule: {error:?}"));

        let reference_context =
            LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, budget_lanes);
        let reference = score_reference(
            &ReferenceGenome::neutral(
                reference_context.n_order_keys(),
                reference_context.n_sites(),
            ),
            &reference_context,
        );
        let committed_score = score_reference(
            &genome_from_schedule(&committed.layers[0], &reference_context),
            &reference_context,
        );

        let context = PlanSearchContext::build_for_roots(
            layer,
            &fields,
            artifact.layers[0].layer,
            budget_cells,
            &compute_roots,
        )
        .unwrap_or_else(|error| panic!("build {stem} context: {error:?}"));
        let neutral_genome = EvaluationGenome::neutral(&context);
        let uncached = context
            .score(&neutral_genome)
            .unwrap_or_else(|error| panic!("score {stem} uncached: {error:?}"));
        let first_fit_natural = score_first_fit(
            layer,
            &fields,
            &context,
            &neutral_genome.root_order_key,
            budget_lanes,
        );
        let first_fit_committed = score_first_fit(
            layer,
            &fields,
            &context,
            &committed_order_keys(&context, &committed.layers[0]),
            budget_lanes,
        );

        println!(
            "eval-plan first-fit: circuit={stem} budget_cells={budget_cells} legacy_lanes={budget_lanes} floor={} established_natural={} \
             established_committed={} uncached={} first_fit_natural={:?} first_fit_committed={:?} \
             elapsed={:?}",
            reference_context.floor,
            reference.dram_traffic,
            committed_score.dram_traffic,
            uncached.fitness.dram_read_lanes,
            first_fit_natural,
            first_fit_committed,
            started.elapsed(),
        );
    }
}
