//! Real-circuit, per-layer forward fixtures for the stage-3 bench
//! (spec: .agents/specs/2026-06-12-gkr-eval-isa-stage3-cuda-bench-design.md §6.0/§6.1).
//!
//! Two pieces:
//! - The CPU-only **consistency precheck** (`assert_layer_consistency`, spec
//!   §6.0): for each circuit, the codegen-IR JSON (`*_codegen_ir_gkr.json`, via
//!   `gkr_design_space::import::load_circuit`) and the prover-side artifact
//!   (`*_layout_gkr.json`, via the test JSON deserializer →
//!   `GKRCircuitArtifact<BF>`) must agree per layer on cache count, cache-out
//!   address set, output address population, and source-column set.
//! - The **per-layer fixture builder** (`build_add_sub_circuit_fixture`, spec
//!   §6.1): drives the REAL add_sub forward preamble + a capturing mirror of
//!   `schedule_layer` that records each flat-side launch into `flat_launches`
//!   so the timed region can replay the recorded sequence. The address→device
//!   pointer map (`addr_resolve`) and the MaxQuadratic scratch reference
//!   (`scratch_ref`) feed the interpreter lowering (`lower.rs`); they are built
//!   here but consumed by the A/B harness in a later task.
//!
//! The capturing pass is FORWARD-ONLY and circuit-agnostic over already
//! constructed prover state. Only the add_sub (unrolled) preamble is wired here
//! (the smoke-test target); see `// Task 6` for the delegation preamble.

use std::collections::{BTreeMap, BTreeSet};

use era_cudart::result::CudaResult;

use super::super::flat_plan::{
    analyze_forward_lookup_usage, build_flat_forward_plan, commit_flat_forward_plan,
    materialize_flat_forward_plan_inits,
};
use super::super::kernels::{
    flat_desc_has_work, launch_flat_forward_layer, launch_forward_cache, FlatForwardPlan,
    GpuFlatForwardStaticDesc, GpuGKRForwardCacheBatch,
};
use super::super::{
    bind_scratch_space_into_storage, build_cache_relation_batches,
    build_materialized_vector_lookup_input_batches, hydrate_scratch_space_layer,
    schedule_materialized_single_lookup_inputs,
};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::setup::{bootstrap_storage_from_trace_holders, GpuGKRForwardSetup};
use crate::prover::gkr::stage1::GpuGKRStage1Output;
use crate::prover::gkr::storage_layout::GpuGKRStorageLayout;
use crate::prover::gkr::transform::normalize_compiled_circuit_for_gpu;
use crate::prover::gkr::{ForwardKernels, GpuGKRStorage};
use crate::prover::ProverContext;
use crate::upstream::{
    GKRAddress, GKRCircuitArtifact, GKRExternalChallenges, GKRLayerDescription, NoFieldGKRRelation,
};

use gkr_design_space::graph::{AnalysisGraph, Origin};

/// Regeneration hint surfaced on any 5.0 precheck mismatch.
pub(crate) const CODEGEN_IR_REGEN_CMD: &str = "cargo test -p cs --release -- --ignored codegen_ir";

/// The three stage-3 circuits, with their compiled-circuit JSON basenames.
pub(crate) const STAGE3_CIRCUITS: [&str; 3] = [
    "add_sub_lui_auipc_mop",
    "bigint_with_extended_control",
    "blake2_with_extended_control",
];

// ===========================================================================
// 5.1 — CPU-only representation-consistency precheck (spec §6.0).
// ===========================================================================

/// Per-layer comparable quantities distilled from ONE representation. Both the
/// codegen-IR layer and the prover artifact layer reduce to the same shape so
/// the precheck is a plain `==` over `GKRAddress` sets, not just counts.
#[derive(Debug, PartialEq, Eq)]
struct LayerConsistencyView {
    cache_count: usize,
    cache_out_addrs: BTreeSet<GKRAddress>,
    output_addrs: BTreeSet<GKRAddress>,
    source_addrs: BTreeSet<GKRAddress>,
}

/// Codegen-IR side: cache outs from `cache.out.1`; outputs from gate `dst`
/// slots; sources from `Place` leaves classified `Origin::InputColumn`
/// (i.e. non-cached, non-scratch circuit input columns). Mirrors
/// `AnalysisGraph::from_layer`'s `Origin` classification (graph.rs).
fn codegen_layer_view(layer: &cs::gkr_compiler::codegen_ir::CodegenLayer) -> LayerConsistencyView {
    let graph = AnalysisGraph::from_layer(layer);
    let cache_count = layer.caches.len();

    let mut cache_out_addrs = BTreeSet::new();
    let mut output_addrs = BTreeSet::new();
    for slot in &graph.outputs {
        if slot.from_cache {
            cache_out_addrs.insert(slot.addr);
        } else {
            output_addrs.insert(slot.addr);
        }
    }

    let source_addrs = graph
        .nodes
        .iter()
        .filter_map(|node| match node.origin {
            Origin::InputColumn(addr) => Some(addr),
            _ => None,
        })
        .collect();

    LayerConsistencyView {
        cache_count,
        cache_out_addrs,
        output_addrs,
        source_addrs,
    }
}

/// Output GKRAddresses a single relation produces. The upstream
/// `NoFieldGKRRelation::dump_outputs` `panic!`s on several output-bearing
/// variants (its catch-all), so the precheck cannot use `outputs()`; this is a
/// complete, explicit replacement over the enum. Constraint-enforcement gates
/// (`EnforceSingleMaxQuadraticConstraint` / `EnforceConstraintsMaxQuadratic`)
/// produce no output — the codegen IR emits no `dst` slot for them either.
pub(crate) fn relation_output_addrs(rel: &NoFieldGKRRelation) -> Vec<GKRAddress> {
    use NoFieldGKRRelation::*;
    match rel {
        EnforceSingleMaxQuadraticConstraint { .. } | EnforceConstraintsMaxQuadratic { .. } => {
            vec![]
        }
        LinearBaseFieldRelation { output, .. }
        | MaxQuadratic { output, .. }
        | CopyInBaseField { output, .. }
        | CopyInExtensionField { output, .. }
        | InitialGrandProductFromCaches { output, .. }
        | InitialGrandProductWithoutCaches { output, .. }
        | UnbalancedGrandProductWithCache { output, .. }
        | MaterializeGrandProductTermExpression { output, .. }
        | TrivialProduct { output, .. }
        | MaskIntoIdentityProduct { output, .. }
        | MaterializeSingleLookupInput { output, .. }
        | MaterializedVectorLookupInput { output, .. }
        | InitsOrTeardownsInitialPair { output, .. } => vec![*output],
        LookupWithCachedDensAndSetup { output, .. }
        | LookupWithDensAndSetupExpressions { output, .. }
        | LookupWithDensAndCachedSetup { output, .. }
        | LookupPairFromBaseInputs { output, .. }
        | LookupPairFromMaterializedBaseInputs { output, .. }
        | LookupFromMaterializedBaseInputWithSetup { output, .. }
        | LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
        | LookupPairFromVectorInputs { output, .. }
        | LookupPairFromMaterializedVectorInputs { output, .. }
        | LookupFromVectorInputWithSetup { output, .. }
        | LookupFromMaterializedVectorInputWithSetup { output, .. }
        | LookupPairFromCachedVectorInputs { output, .. }
        | LookupUnbalancedPairWithVectorInputs { output, .. }
        | LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
        | AggregateLookupRationalPair { output, .. } => output.to_vec(),
    }
}

/// Per-gate input addresses, robust against the upstream `dump_inputs`
/// catch-all `panic!`. Across the 3 stage-3 circuits the only input-bearing
/// variant `dump_inputs` panics on is `LookupUnbalancedPairWithMaterializedVectorInputs`
/// (simple `[GKRAddress;2]` + `remainder`); handle it explicitly and defer all
/// other census variants to upstream `dump_inputs` (no nested-relation walk to
/// reimplement). A future panic-prone variant fails loudly inside `dump_inputs`.
fn collect_relation_inputs(rel: &NoFieldGKRRelation, out: &mut BTreeSet<GKRAddress>) {
    match rel {
        NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
            input,
            remainder,
            ..
        } => {
            out.insert(input[0]);
            out.insert(input[1]);
            out.insert(*remainder);
        }
        other => other.dump_inputs(out),
    }
}

/// Prover-artifact side: cache outs are the `cached_relations` map keys; the
/// output set is the per-gate `relation_output_addrs` union (a robust
/// replacement for the panic-prone `outputs()`); the source set is the UNION of
/// gate inputs (`collect_relation_inputs`) and cache-relation dependencies,
/// filtered to non-`Cached`/non-`Scratch` addresses (the codegen IR's
/// `InputColumn` set already includes cache-input reads, so gate inputs alone
/// undercount).
fn artifact_layer_view(layer: &GKRLayerDescription) -> LayerConsistencyView {
    let cache_count = layer.cached_relations.len();
    let cache_out_addrs: BTreeSet<GKRAddress> = layer.cached_relations.keys().copied().collect();

    let mut output_addrs: BTreeSet<GKRAddress> = BTreeSet::new();
    let mut gate_inputs: BTreeSet<GKRAddress> = BTreeSet::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        output_addrs.extend(relation_output_addrs(&gate.enforced_relation));
        collect_relation_inputs(&gate.enforced_relation, &mut gate_inputs);
    }

    let mut source_addrs: BTreeSet<GKRAddress> = gate_inputs
        .into_iter()
        .filter(|a| !matches!(a, GKRAddress::Cached { .. } | GKRAddress::ScratchSpace(_)))
        .collect();
    for relation in layer.cached_relations.values() {
        for dep in relation.dependencies() {
            if !matches!(dep, GKRAddress::Cached { .. } | GKRAddress::ScratchSpace(_)) {
                source_addrs.insert(dep);
            }
        }
    }

    LayerConsistencyView {
        cache_count,
        cache_out_addrs,
        output_addrs,
        source_addrs,
    }
}

/// 5.0 precheck for one circuit: load BOTH representations and assert per-layer
/// agreement. Panics (with the regen hint) on any mismatch. CPU-only.
pub(crate) fn assert_layer_consistency(circuit: &str) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let codegen =
        gkr_design_space::import::load_circuit(&dir.join(format!("{circuit}_codegen_ir_gkr.json")))
            .unwrap_or_else(|e| panic!("{circuit}: failed to load codegen IR: {e}"));
    let artifact: GKRCircuitArtifact<BF> = crate::prover::tests::deserialize_json_for_test(
        &format!("cs/compiled_circuits/{circuit}_layout_gkr.json"),
    );

    let codegen_layers = &codegen.circuit.layers;
    assert_eq!(
        codegen_layers.len(),
        artifact.layers.len(),
        "{circuit}: layer count mismatch (codegen IR {} vs artifact {}); regen: {CODEGEN_IR_REGEN_CMD}",
        codegen_layers.len(),
        artifact.layers.len(),
    );

    for (layer_idx, (cg_layer, art_layer)) in codegen_layers
        .iter()
        .zip(artifact.layers.iter())
        .enumerate()
    {
        let cg = codegen_layer_view(cg_layer);
        let art = artifact_layer_view(art_layer);
        assert_eq!(
            cg.cache_count, art.cache_count,
            "{circuit} layer {layer_idx}: cache count (codegen IR {} vs artifact {}); regen: {CODEGEN_IR_REGEN_CMD}",
            cg.cache_count, art.cache_count,
        );
        assert_eq!(
            cg.cache_out_addrs, art.cache_out_addrs,
            "{circuit} layer {layer_idx}: cache-out address set mismatch; regen: {CODEGEN_IR_REGEN_CMD}",
        );
        assert_eq!(
            cg.output_addrs, art.output_addrs,
            "{circuit} layer {layer_idx}: output address population mismatch; regen: {CODEGEN_IR_REGEN_CMD}",
        );
        assert_eq!(
            cg.source_addrs, art.source_addrs,
            "{circuit} layer {layer_idx}: source-column set mismatch; regen: {CODEGEN_IR_REGEN_CMD}",
        );
    }
}

// ===========================================================================
// 5.2 — Per-layer fixture types + capturing schedule_layer mirror (spec §6.1).
// ===========================================================================

/// One replayable flat-side launch, captured at the launcher boundary. The
/// embedded descriptors/batches hold raw pointers into `GpuGKRStorage`-owned
/// allocations; the owning `CircuitFixture` keeps that storage alive for the
/// lifetime of every replay.
pub(crate) enum FlatLaunch {
    /// Cache-relation batch (`schedule_cache_relations` →
    /// `build_cache_relation_batches`), launched via `launch_forward_cache`.
    Cache(GpuGKRForwardCacheBatch<E4>),
    /// `MaterializedVectorLookupInput` cache batch
    /// (`build_materialized_vector_lookup_input_batches`).
    MaterializeVec(GpuGKRForwardCacheBatch<E4>),
    /// Flat category-table descriptor (`build_flat_forward_plan`), launched via
    /// `launch_flat_forward_layer`. Only descs with work are recorded.
    Desc(Box<GpuFlatForwardStaticDesc<E4>>),
    /// `InitsOrTeardownsInitialPair` deferred materialization, re-launched from
    /// the captured plan via `materialize_flat_forward_plan_inits`.
    Inits(FlatForwardPlan<E4>),
    /// `MaterializeSingleLookupInput` / `LinearBaseFieldRelation` inline
    /// materialization. Launched once during fixture construction; NOT yet
    /// replayable (its production launcher is not build/launch split). add_sub
    /// L0 never hits this; bigint/blake2 do.
    // Task 6: build/launch split for schedule_materialized_single_lookup_inputs
    // so this launch becomes replayable for the multi-circuit A/B.
    MaterializeSingle,
}

/// Per-layer fixture (spec §6.1): the replayable flat-launch sequence plus the
/// address→pointer maps the interpreter lowering consumes.
pub(crate) struct LayerFixture {
    pub(crate) layer_idx: usize,
    /// Replayable launches, in production launch order.
    pub(crate) flat_launches: Vec<FlatLaunch>,
    /// src + dst GKRAddress → device base pointer (resolved through the same
    /// storage accessors `build_flat_forward_plan` uses). For `lower.rs`'s
    /// resolver closures — consumed by the interpreter A/B in a later task.
    // Task 6: wired into lower_program / lower_payloads for the interpreter side.
    #[allow(dead_code)]
    pub(crate) addr_resolve: BTreeMap<GKRAddress, *const u8>,
    /// Hydrated MaxQuadratic scratch reference values (the witness-stage scratch
    /// production trusts): scratch GKRAddress → device base pointer.
    // Task 6: the equal-work row's MaxQuadratic input reference.
    #[allow(dead_code)]
    pub(crate) scratch_ref: Vec<(GKRAddress, *const u8)>,
    #[allow(dead_code)]
    pub(crate) trace_len: usize,
}

/// Per-circuit fixture: owns everything the per-layer launches and pointer maps
/// reference (storage backings, stage1, forward setup, the base test fixture
/// holding `ProverContext`), so the `LayerFixture` raw pointers stay valid for
/// the duration of every replay. Forward-only.
pub(crate) struct CircuitFixture {
    /// Keeps `ProverContext` + all H2D'd backings alive; also the access path to
    /// the context for replay launches.
    pub(crate) base: crate::prover::tests::BasicUnrolledFixture,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E4>,
    pub(crate) trace_len: usize,
    /// Forward storage AFTER the capturing pass (all real outputs resident).
    pub(crate) storage: GpuGKRStorage<BF, E4>,
    pub(crate) layers: Vec<LayerFixture>,
    /// Kept alive: forward-setup lookup buffers + stage1 mappings/scratch that
    /// the captured launches reference.
    #[allow(dead_code)]
    pub(crate) stage1: GpuGKRStage1Output,
    #[allow(dead_code)]
    pub(crate) forward_setup: GpuGKRForwardSetup<E4>,
}

impl CircuitFixture {
    /// Replay every captured flat launch of `layer_idx` in production order.
    /// Replayable launches re-issue the SAME kernels into the SAME storage
    /// buffers (idempotent given the resident source columns); the result is
    /// the layer's real flat-side outputs. Test code — synchronization is the
    /// caller's responsibility (see the smoke test).
    pub(crate) fn replay_layer(&self, layer_idx: usize) -> CudaResult<()> {
        let context = &self.base.context;
        let trace_len = self.trace_len;
        let layer = &self.layers[layer_idx];
        for launch in &layer.flat_launches {
            match launch {
                FlatLaunch::Cache(batch) | FlatLaunch::MaterializeVec(batch) => {
                    launch_forward_cache(*batch, trace_len, context)?;
                }
                FlatLaunch::Desc(desc) => {
                    launch_flat_forward_layer(desc, trace_len, context)?;
                }
                FlatLaunch::Inits(plan) => {
                    materialize_flat_forward_plan_inits(
                        plan,
                        &self.storage,
                        &self.external_challenges,
                        trace_len,
                        context,
                    )?;
                }
                FlatLaunch::MaterializeSingle => {
                    // Not replayable yet (see the variant doc / Task 6 seam).
                }
            }
        }
        Ok(())
    }
}

/// Build the layer's address→pointer map from the storage accessors, covering
/// every base/ext source the flat plan reads and every output the layer
/// produces. Iterates the layer's gate + cache relations to discover the
/// addresses, then resolves each through `try_get_base_poly`/`try_get_ext_poly`
/// (the same accessors `build_flat_forward_plan` uses).
fn build_addr_resolve(
    layer: &GKRLayerDescription,
    storage: &GpuGKRStorage<BF, E4>,
) -> BTreeMap<GKRAddress, *const u8> {
    // Use the panic-robust extractors (not `inputs()`/`outputs()`, which the
    // upstream `dump_*` catch-alls can `panic!` on — see the 5.1 precheck).
    let mut addrs: BTreeSet<GKRAddress> = BTreeSet::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        collect_relation_inputs(&gate.enforced_relation, &mut addrs);
        addrs.extend(relation_output_addrs(&gate.enforced_relation));
    }
    addrs.extend(layer.cached_relations.keys().copied());
    for relation in layer.cached_relations.values() {
        addrs.extend(relation.dependencies());
    }

    let mut map = BTreeMap::new();
    for addr in addrs {
        let ptr = if let Some(p) = storage.try_get_base_poly(addr) {
            p.as_ptr() as *const u8
        } else if let Some(p) = storage.try_get_ext_poly(addr) {
            p.as_ptr() as *const u8
        } else {
            // Addresses produced later in this same layer's scheduling are not
            // yet resident at map-build time; the interpreter lowering only
            // needs the inputs that ARE resident. Skip the rest.
            continue;
        };
        map.insert(addr, ptr);
    }
    map
}

/// The hydrated MaxQuadratic scratch reference for a layer: every
/// `ScratchSpace`/`InnerLayer` scratch address mapped at this layer, resolved to
/// its hydrated base-poly device pointer (the witness-stage scratch values, the
/// equal-work row's MaxQuadratic input == production's flat reference).
fn build_scratch_ref(
    layer_idx: usize,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    storage: &GpuGKRStorage<BF, E4>,
) -> Vec<(GKRAddress, *const u8)> {
    let mut out = Vec::new();
    for (_scratch_idx, address) in compiled_circuit.scratch_space_mapping_rev.iter() {
        let resident = match address {
            GKRAddress::InnerLayer { layer, .. } if *layer == layer_idx => true,
            GKRAddress::ScratchSpace(_) if layer_idx == 0 => true,
            _ => false,
        };
        if !resident {
            continue;
        }
        if let Some(poly) = storage.try_get_base_poly(*address) {
            out.push((*address, poly.as_ptr() as *const u8));
        }
    }
    out
}

/// Capturing mirror of `schedule_layer` (forward/mod.rs): call the SAME build
/// functions (which mutate `storage` exactly as production does) and launch
/// each immediately to populate `storage` for later layers, while ALSO
/// recording every launch into `flat_launches`. Returns the per-layer fixture.
///
/// `MaterializeSingle` is launched (its production launcher is not split) but
/// recorded as a non-replayable marker (Task 6 seam).
#[allow(clippy::too_many_arguments)]
fn capture_layer(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    storage: &mut GpuGKRStorage<BF, E4>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E4>,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    decoder_predicate_address: Option<GKRAddress>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<LayerFixture> {
    hydrate_scratch_space_layer(layer_idx, compiled_circuit, stage1, storage);

    let scratch_ref = build_scratch_ref(layer_idx, compiled_circuit, storage);

    let mut flat_launches = Vec::new();

    // (1) cache relations.
    let cache_batches = build_cache_relation_batches(
        layer_idx,
        &layer.cached_relations,
        storage,
        stage1,
        forward_setup,
        external_challenges,
        decoder_predicate_address,
        trace_len,
        context,
    )?;
    for batch in cache_batches {
        launch_forward_cache(batch, trace_len, context)?;
        flat_launches.push(FlatLaunch::Cache(batch));
    }

    let expected_output_layer = layer_idx + 1;

    // (2) MaterializedVectorLookupInput caches.
    let vec_batches = build_materialized_vector_lookup_input_batches(
        expected_output_layer,
        layer,
        storage,
        stage1,
        forward_setup,
        decoder_predicate_address,
        context,
    )?;
    for batch in vec_batches {
        launch_forward_cache(batch, trace_len, context)?;
        flat_launches.push(FlatLaunch::MaterializeVec(batch));
    }

    // (3) MaterializeSingleLookupInput / LinearBaseFieldRelation (inline; not
    // yet split — launched here, recorded as a non-replayable marker).
    let has_single = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .any(|gate| {
            matches!(
                &gate.enforced_relation,
                NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
                    | NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            )
        });
    schedule_materialized_single_lookup_inputs(
        expected_output_layer,
        layer,
        storage,
        trace_len,
        context,
    )?;
    if has_single {
        flat_launches.push(FlatLaunch::MaterializeSingle);
    }

    // (4) flat plan: build, launch deferred inits, then the chunked descs.
    let plan = build_flat_forward_plan(
        layer_idx,
        &layer.gates,
        &layer.gates_with_external_connections,
        stage1,
        forward_setup,
        decoder_predicate_address,
        &compiled_circuit.scratch_space_mapping,
        storage,
        external_challenges,
        trace_len,
        context,
    )?;
    materialize_flat_forward_plan_inits(&plan, storage, external_challenges, trace_len, context)?;
    if !plan.pending_inits.is_empty() {
        // Capture a plan carrying ONLY the deferred inits (the dst views are
        // shared clones; the desc/output vecs are not needed for replay).
        flat_launches.push(FlatLaunch::Inits(FlatForwardPlan {
            descs: Vec::new(),
            computed_extension_outputs: Vec::new(),
            aliased_base_outputs: Vec::new(),
            aliased_extension_outputs: Vec::new(),
            pending_inits: plan
                .pending_inits
                .iter()
                .map(|p| super::super::kernels::PendingInitsLaunch {
                    dst: p.dst.clone_shared(),
                    timestamp_and_value: p.timestamp_and_value.clone(),
                    setup: p.setup,
                    address_high_bits: p.address_high_bits,
                    address_high_bits_shift: p.address_high_bits_shift,
                })
                .collect(),
        }));
    }
    for desc in plan.descs.iter() {
        if flat_desc_has_work(desc) {
            launch_flat_forward_layer(desc, trace_len, context)?;
            flat_launches.push(FlatLaunch::Desc(desc.clone()));
        }
    }
    commit_flat_forward_plan(expected_output_layer, storage, plan);

    let addr_resolve = build_addr_resolve(layer, storage);

    Ok(LayerFixture {
        layer_idx,
        flat_launches,
        addr_resolve,
        scratch_ref,
        trace_len,
    })
}

/// Build the per-circuit forward fixture for `add_sub` (the smoke-test target).
/// Runs the REAL unrolled preamble (artifact + trace + stage1 + forward setup),
/// then a capturing forward pass that mirrors `schedule_forward_pass`'s preamble
/// and per-layer body WITHOUT the dimension-reduction tail.
///
/// The lookup-resource releases that production performs mid-pass are skipped
/// here so the captured launch pointers (mappings / generic-lookup) remain
/// resident for replay — a forward-only test concession that only keeps more
/// buffers alive, never fewer.
//
// Task 6: delegation preamble for bigint/blake2 (their fixtures are first needed
// by the multi-circuit A/B; 5.1 already covers all 3 at the artifact level).
pub(crate) fn build_add_sub_circuit_fixture() -> CircuitFixture {
    let (base, _expected_cpu_proof) =
        crate::prover::tests::prepare_basic_unrolled_add_sub_fixture_for_bench();

    // Run the real forward preamble, then the capturing pass inside the callback
    // (which owns the `gkr::forward`-private scheduling helpers). The callback
    // returns the populated storage + per-layer fixtures + the normalized
    // circuit; `stage1`/`forward_setup` are returned alongside so we keep them
    // alive (their device buffers back the captured launch pointers).
    let (
        stage1,
        forward_setup,
        (compiled_circuit, external_challenges, trace_len, storage, layers),
    ) = crate::prover::tests::build_basic_unrolled_forward_capture(&base, |refs| {
        capture_forward_pass(refs)
    });

    CircuitFixture {
        base,
        compiled_circuit,
        external_challenges,
        trace_len,
        storage,
        layers,
        stage1,
        forward_setup,
    }
}

type CaptureResult = (
    GKRCircuitArtifact<BF>,
    GKRExternalChallenges<BF, E4>,
    usize,
    GpuGKRStorage<BF, E4>,
    Vec<LayerFixture>,
);

/// Forward-only capturing pass: mirror `schedule_forward_pass`'s preamble
/// (storage bootstrap → layout → scratch bind → gamma prelude) and per-layer
/// body (`capture_layer`), WITHOUT the dimension-reduction tail. The mid-pass
/// lookup-resource releases production performs are intentionally skipped so the
/// captured launch pointers (mappings / generic-lookup) stay resident for
/// replay — a forward-only test concession that only keeps more buffers alive.
fn capture_forward_pass(
    refs: crate::prover::tests::BasicUnrolledForwardPreambleRefs<'_>,
) -> CaptureResult {
    let context = refs.context;
    let compiled_circuit = normalize_compiled_circuit_for_gpu(refs.compiled_circuit.clone());
    let external_challenges = refs.external_challenges.clone();
    let trace_len = compiled_circuit.trace_len;
    let setup_trace_holder = refs.setup_trace_holder;
    let stage1 = refs.stage1;
    let forward_setup = refs.forward_setup;

    let mut storage: GpuGKRStorage<BF, E4> = bootstrap_storage_from_trace_holders::<E4>(
        Some(setup_trace_holder),
        setup_trace_holder.columns_count,
        setup_trace_holder.log_domain_size,
        setup_trace_holder.log_lde_factor,
        setup_trace_holder.log_rows_per_leaf,
        setup_trace_holder.log_tree_cap_size,
        &stage1.memory_trace_holder,
        &stage1.witness_trace_holder,
        context,
    )
    .unwrap();
    let storage_layout = std::sync::Arc::new(GpuGKRStorageLayout::from_artifact_with_tower(
        &compiled_circuit,
        refs.final_trace_size_log_2,
    ));
    storage.set_layout(storage_layout);
    bind_scratch_space_into_storage(&compiled_circuit, stage1, &mut storage);

    // Validate the usage analysis runs (it panics on an unsupported relation);
    // the releases themselves are intentionally skipped (see the doc comment).
    let _usage = analyze_forward_lookup_usage(&compiled_circuit);

    E4::schedule_lookup_gamma_consts_prelude(
        forward_setup.lookup_additive_part_device().as_ptr(),
        context,
    )
    .unwrap();

    let decoder_predicate_address = compiled_circuit
        .memory_layout
        .machine_state
        .as_ref()
        .map(|machine_state| GKRAddress::BaseLayerMemory(machine_state.execute));

    let mut layers = Vec::with_capacity(compiled_circuit.layers.len());
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        let fixture = capture_layer(
            layer_idx,
            layer,
            &compiled_circuit,
            &mut storage,
            stage1,
            forward_setup,
            &external_challenges,
            decoder_predicate_address,
            trace_len,
            context,
        )
        .unwrap();
        layers.push(fixture);
    }
    context.get_exec_stream().synchronize().unwrap();

    (
        compiled_circuit,
        external_challenges,
        trace_len,
        storage,
        layers,
    )
}
