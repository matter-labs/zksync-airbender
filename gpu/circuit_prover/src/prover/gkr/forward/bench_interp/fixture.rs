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
    GpuFlatForwardStaticDesc, GpuGKRForwardCacheBatch, PendingInitsLaunch,
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
use crate::prover::trace::holder::TraceHolder;
use crate::prover::ProverContext;
use crate::upstream::{
    GKRAddress, GKRCircuitArtifact, GKRExternalChallenges, GKRLayerDescription, NoFieldGKRRelation,
    TableType, VirtualSetupPoly,
};

use cs::gkr_compiler::codegen_ir::{CodegenLayer, ExprNode, ProducerId};
use field::{Field, FieldExtension, PrimeField};
use gkr_design_space::graph::{AnalysisGraph, Origin};
use gkr_eval_isa::compiler::fwd::{CompiledForward, PayloadRecord};

use super::lower::BenchChallenges;

/// Regeneration hint surfaced on any 5.1 precheck mismatch.
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

/// 5.1 precheck for one circuit: load BOTH representations and assert per-layer
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

/// Per-circuit keepalive: owns the family-specific preamble state (transfers,
/// setup host/transfer, trace, the base test fixture) whose device buffers back
/// the captured launch pointers + the `addr_resolve` map. Held opaquely so the
/// `LayerFixture` raw pointers stay valid for the lifetime of every replay.
pub(crate) enum CircuitKeepalive {
    /// add_sub (unrolled): the base fixture + the moved-out stage1/forward-setup
    /// from `build_basic_unrolled_forward_capture`.
    Unrolled {
        base: crate::prover::tests::BasicUnrolledFixture,
        /// Held only to keep its device buffers (mappings/scratch) alive for the
        /// captured launch pointers; never read directly.
        #[allow(dead_code)]
        stage1: GpuGKRStage1Output,
        forward_setup: GpuGKRForwardSetup<E4>,
    },
    /// bigint / blake2 (delegation): the owned context + the preamble keepalive
    /// bundle built by `build_delegation_forward_capture`.
    Delegation(Box<crate::prover::tests::DelegationForwardCaptureKeepalive>),
}

/// Per-circuit fixture: owns everything the per-layer launches and pointer maps
/// reference (storage backings, stage1, forward setup, the family-specific
/// keepalive holding `ProverContext`), so the `LayerFixture` raw pointers stay
/// valid for the duration of every replay. Forward-only.
pub(crate) struct CircuitFixture {
    /// Keeps all family-specific H2D'd backings alive (incl. the owning
    /// `ProverContext`); the access path to the context for replay launches.
    pub(crate) keepalive: CircuitKeepalive,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E4>,
    pub(crate) trace_len: usize,
    /// Forward storage AFTER the capturing pass (all real outputs resident).
    pub(crate) storage: GpuGKRStorage<BF, E4>,
    pub(crate) layers: Vec<LayerFixture>,
    /// Lookup folding challenge (`lookup_alpha`) captured at the draw site;
    /// feeds `BenchChallenges::alpha` and the decoder-fill recovery.
    pub(crate) lookup_alpha: E4,
    /// Lookup additive part (`lookup_additive_part`); equals `BenchChallenges::
    /// gamma` and the device-staged `ab_gkr_lookup_gamma_consts` base value.
    pub(crate) lookup_additive_part: E4,
}

/// Deep-clone the captured deferred-inits launches (the dst views are shared
/// clones). Used both to capture a replayable copy before
/// `materialize_flat_forward_plan_inits` drains the source plan, and to launch
/// each replay from a fresh, drainable copy without consuming the captured one.
fn clone_pending_inits(pending: &[PendingInitsLaunch<E4>]) -> Vec<PendingInitsLaunch<E4>> {
    pending
        .iter()
        .map(|p| PendingInitsLaunch {
            dst: p.dst.clone_shared(),
            timestamp_and_value: p.timestamp_and_value.clone(),
            setup: p.setup,
            address_high_bits: p.address_high_bits,
            address_high_bits_shift: p.address_high_bits_shift,
        })
        .collect()
}

impl CircuitKeepalive {
    /// The owning `ProverContext` (the replay launches issue onto its streams).
    pub(crate) fn context(&self) -> &ProverContext {
        match self {
            CircuitKeepalive::Unrolled { base, .. } => &base.context,
            CircuitKeepalive::Delegation(keepalive) => &keepalive.context,
        }
    }

    /// The forward setup whose `generic_lookup()` buffer is the device base of
    /// the single `VectorizedLookupSetup` cache out (the interpreter's setup
    /// table). Same buffer the flat path's setup cache reads from.
    pub(crate) fn forward_setup(&self) -> &GpuGKRForwardSetup<E4> {
        match self {
            CircuitKeepalive::Unrolled { forward_setup, .. } => forward_setup,
            CircuitKeepalive::Delegation(keepalive) => &keepalive.forward_setup,
        }
    }
}

impl CircuitFixture {
    /// The decoder execute-predicate address (`BaseLayerMemory(machine_state.
    /// execute)`), or `None` when the circuit has no machine state (delegation).
    /// Derived once from the normalized circuit; layer-independent.
    pub(crate) fn decoder_predicate_address(&self) -> Option<GKRAddress> {
        self.compiled_circuit
            .memory_layout
            .machine_state
            .as_ref()
            .map(|machine_state| GKRAddress::BaseLayerMemory(machine_state.execute))
    }

    /// `(generic_lookup device base, valid length)` — the single
    /// `VectorizedLookupSetup` cache out (the interpreter's setup table).
    pub(crate) fn setup_table(&self) -> (*const u8, u32) {
        let fs = self.keepalive.forward_setup();
        (
            fs.generic_lookup().as_ptr() as *const u8,
            fs.generic_lookup_len() as u32,
        )
    }

    /// Resolve a GKRAddress to its resident device column in the POST-CAPTURE
    /// storage (every layer's outputs + hydrated scratch are bound). Returns
    /// `(is_e4, base ptr)`. Unlike a per-layer `addr_resolve`, this sees
    /// next-layer hydrated MaxQuadratic scratch (`InnerLayer { layer: L+1 }`),
    /// the flat reference for an MQ gate dst at layer L.
    pub(crate) fn storage_column(&self, addr: GKRAddress) -> Option<(bool, *const u8)> {
        if let Some(p) = self.storage.try_get_base_poly(addr) {
            Some((false, p.as_ptr() as *const u8))
        } else {
            self.storage
                .try_get_ext_poly(addr)
                .map(|p| (true, p.as_ptr() as *const u8))
        }
    }

    /// The flat reference column for payload `p`'s j-th dst: the resident
    /// storage column at the gate's `dst[j].addr` / cache `out.1` (MaxQuadratic
    /// gate dsts resolve to the hydrated witness-stage scratch value).
    pub(crate) fn payload_dst_reference(
        &self,
        cf: &CompiledForward,
        p: usize,
        j: usize,
    ) -> (bool, *const u8) {
        let addr = match &cf.payloads[p] {
            PayloadRecord::Gate(g) => g.dst[j].addr,
            PayloadRecord::Cache(c) => {
                assert_eq!(j, 0, "cache payload {p} has a single dst");
                c.out.1
            }
        };
        self.storage_column(addr).unwrap_or_else(|| {
            panic!(
                "payload_dst_reference: payload {p} dst {j} addr {addr:?} not resident in storage"
            )
        })
    }
}

impl CircuitFixture {
    /// The owning `ProverContext` for this fixture's replay/A-B launches.
    pub(crate) fn context(&self) -> &ProverContext {
        self.keepalive.context()
    }

    /// Assemble the interpreter's `BenchChallenges` from the captured lookup
    /// challenges + the fixture's external (memory-argument) challenges. Each
    /// field is sourced exactly as the production forward path consumes it
    /// (see the field docs).
    pub(crate) fn bench_challenges(&self) -> BenchChallenges {
        let perm = &self
            .external_challenges
            .permutation_argument_linearization_challenges;
        // Roles ADDR_LOW..VAL_HIGH = the first 6 linearization challenges; same
        // index convention as lower.rs and the flat permutation-argument path.
        let perm_challenges: [E4; 6] = std::array::from_fn(|role| perm[role]);

        // decoder_fill = lookup_alpha^(generic_width-1) * TableType::Decoder,
        // only when the circuit carries table-ids in its generic lookups
        // (forward setup's `tables_ids_in_generic_lookups` gate); else ZERO.
        let decoder_fill = if self.compiled_circuit.tables_ids_in_generic_lookups {
            let width = self.compiled_circuit.generic_lookup_tables_width;
            assert!(width > 0, "tables_ids_in_generic_lookups with zero width");
            let mut t = self.lookup_alpha.pow((width - 1) as u32);
            t.mul_assign_by_base(&BF::from_u32_unchecked(TableType::Decoder as u32));
            t
        } else {
            E4::ZERO
        };

        BenchChallenges {
            // gamma == lookup_additive_part; the routines read [g, g^2, 2g] from
            // the `ab_gkr_lookup_gamma_consts` symbol that the flat preamble's
            // `schedule_lookup_gamma_consts_prelude` already staged from this
            // exact value — so the real-fixture run must NOT re-stage it.
            gamma: self.lookup_additive_part,
            alpha: self.lookup_alpha,
            perm_challenges,
            perm_additive: self.external_challenges.permutation_argument_additive_part,
            decoder_fill,
        }
    }

    /// Replay every captured flat launch of `layer_idx` in production order.
    /// Replayable launches re-issue the SAME kernels into the SAME storage
    /// buffers (idempotent given the resident source columns); the result is
    /// the layer's real flat-side outputs. Test code — synchronization is the
    /// caller's responsibility (see the smoke test).
    pub(crate) fn replay_layer(&self, layer_idx: usize) -> CudaResult<()> {
        let context = self.context();
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
                    // `materialize_flat_forward_plan_inits` DRAINS the plan it is
                    // given. Replay must be repeatable (replay-twice identical),
                    // so launch from a fresh clone and leave the captured plan
                    // intact for the next replay.
                    let mut replay_plan = FlatForwardPlan {
                        descs: Vec::new(),
                        computed_extension_outputs: Vec::new(),
                        aliased_base_outputs: Vec::new(),
                        aliased_extension_outputs: Vec::new(),
                        pending_inits: clone_pending_inits(&plan.pending_inits),
                    };
                    materialize_flat_forward_plan_inits(
                        &mut replay_plan,
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
/// Intentionally mirrors the **UNFUSED** `schedule_layer` body only: it does
/// NOT reproduce the `generated_layer0` fused A/B early-return path that
/// `schedule_layer` takes when `AB_GKR_FWD_GENERATED_LAYER0` is active. The
/// fixture wants the per-launch flat sequence as the bench baseline, so omitting
/// the fused path is deliberate, not an oversight.
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
    // Keep the fixture honest about the captured layer shape, matching the
    // invariant `schedule_layer` asserts before scheduling a layer.
    super::super::assert_forward_layer_invariants(layer_idx, compiled_circuit.layers.len(), layer);

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
    let mut plan = build_flat_forward_plan(
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
    // Capture the deferred inits for replay BEFORE materializing — the
    // materialize step DRAINS `plan.pending_inits`, so reading it afterward
    // would see an empty field. The captured plan carries ONLY the deferred
    // inits (the dst views are shared clones; the desc/output vecs are not
    // needed for replay).
    if !plan.pending_inits.is_empty() {
        flat_launches.push(FlatLaunch::Inits(FlatForwardPlan {
            descs: Vec::new(),
            computed_extension_outputs: Vec::new(),
            aliased_base_outputs: Vec::new(),
            aliased_extension_outputs: Vec::new(),
            pending_inits: clone_pending_inits(&plan.pending_inits),
        }));
    }
    materialize_flat_forward_plan_inits(
        &mut plan,
        storage,
        external_challenges,
        trace_len,
        context,
    )?;
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

impl CircuitFixture {
    /// Build the per-circuit forward fixture, dispatching by circuit family:
    /// `add_sub_lui_auipc_mop` → the unrolled preamble; `bigint_*`/`blake2_*` →
    /// the delegation preamble. Both drive the SAME `capture_forward_pass`.
    pub(crate) fn build(circuit: &str) -> CircuitFixture {
        match circuit {
            "add_sub_lui_auipc_mop" => build_add_sub_circuit_fixture(),
            "bigint_with_extended_control" | "blake2_with_extended_control" => {
                build_delegation_circuit_fixture(circuit)
            }
            other => panic!("CircuitFixture::build: unsupported circuit {other}"),
        }
    }
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
pub(crate) fn build_add_sub_circuit_fixture() -> CircuitFixture {
    let (base, _expected_cpu_proof) =
        crate::prover::tests::prepare_basic_unrolled_add_sub_fixture_for_bench();

    // Run the real forward preamble, then the capturing pass inside the callback
    // (which owns the `gkr::forward`-private scheduling helpers). The callback
    // returns the populated storage + per-layer fixtures + the normalized
    // circuit; `stage1`/`forward_setup` are returned alongside so we keep them
    // alive (their device buffers back the captured launch pointers).
    let mut captured_challenges = (E4::ZERO, E4::ZERO);
    let (
        stage1,
        forward_setup,
        (compiled_circuit, external_challenges, trace_len, storage, layers),
    ) = crate::prover::tests::build_basic_unrolled_forward_capture(&base, |refs| {
        captured_challenges = (refs.lookup_alpha, refs.lookup_additive_part);
        capture_forward_pass(
            refs.context,
            Some(refs.setup_trace_holder),
            refs.stage1,
            refs.forward_setup,
            refs.compiled_circuit,
            refs.external_challenges,
            refs.final_trace_size_log_2,
        )
    });
    let (lookup_alpha, lookup_additive_part) = captured_challenges;

    CircuitFixture {
        keepalive: CircuitKeepalive::Unrolled {
            base,
            stage1,
            forward_setup,
        },
        compiled_circuit,
        external_challenges,
        trace_len,
        storage,
        layers,
        lookup_alpha,
        lookup_additive_part,
    }
}

/// Build the per-circuit forward fixture for a delegation circuit (bigint /
/// blake2). Runs the REAL delegation preamble (trace replay → stage1 → forward
/// setup, via `build_delegation_forward_capture`), then the SAME capturing
/// forward pass as add_sub. The delegation setup trace holder carries the
/// `generic_lookup_tables_width` setup columns (the `Setup(0..)` sources), so
/// it is passed through to the storage bootstrap.
fn build_delegation_circuit_fixture(circuit: &str) -> CircuitFixture {
    let mut captured: Option<(E4, E4, CaptureResult)> = None;
    let keepalive = crate::prover::tests::build_delegation_forward_capture(circuit, |refs| {
        let result = capture_forward_pass(
            refs.context,
            Some(refs.setup_trace_holder),
            refs.stage1,
            refs.forward_setup,
            refs.compiled_circuit,
            refs.external_challenges,
            refs.final_trace_size_log_2,
        );
        captured = Some((refs.lookup_alpha, refs.lookup_additive_part, result));
    });
    let (
        lookup_alpha,
        lookup_additive_part,
        (compiled_circuit, external_challenges, trace_len, storage, layers),
    ) = captured.expect("delegation capture callback did not run");

    CircuitFixture {
        keepalive: CircuitKeepalive::Delegation(Box::new(keepalive)),
        compiled_circuit,
        external_challenges,
        trace_len,
        storage,
        layers,
        lookup_alpha,
        lookup_additive_part,
    }
}

pub(crate) type CaptureResult = (
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
///
/// `setup_trace_holder` is `None` for delegation circuits (zero uploaded setup
/// columns), matching production's `synthetic_setup_trace_holder` branch; when
/// present it carries the resident setup columns (add_sub). The storage
/// bootstrap binds zero setup columns in the None case.
#[allow(clippy::too_many_arguments)]
fn capture_forward_pass(
    context: &ProverContext,
    setup_trace_holder: Option<&TraceHolder<BF>>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E4>,
    raw_compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    final_trace_size_log_2: usize,
) -> CaptureResult {
    let compiled_circuit = normalize_compiled_circuit_for_gpu(raw_compiled_circuit.clone());
    let external_challenges = *external_challenges;
    let trace_len = compiled_circuit.trace_len;

    // Bootstrap exactly as production: Some(holder) for an uploaded setup
    // (add_sub), None for the zero-column delegation case. The column count is
    // the holder's own (0 for delegation), which the bootstrap asserts.
    let setup_columns_count = setup_trace_holder.map_or(0, |h| h.columns_count);
    // Trace geometry: prefer the setup holder, else the memory holder (the
    // delegation case lacks a setup holder but all three holders share geometry,
    // which `bootstrap_storage_from_trace_holders` asserts).
    let geom = setup_trace_holder.unwrap_or(&stage1.memory_trace_holder);
    let mut storage: GpuGKRStorage<BF, E4> = bootstrap_storage_from_trace_holders::<E4>(
        setup_trace_holder,
        setup_columns_count,
        geom.log_domain_size,
        geom.log_lde_factor,
        geom.log_rows_per_leaf,
        geom.log_tree_cap_size,
        &stage1.memory_trace_holder,
        &stage1.witness_trace_holder,
        context,
    )
    .unwrap();
    let storage_layout = std::sync::Arc::new(GpuGKRStorageLayout::from_artifact_with_tower(
        &compiled_circuit,
        final_trace_size_log_2,
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

// ===========================================================================
// Task 6.B — real-fixture resolvers (the three-key-space leaf → device pointer
// mapping the interpreter lowering consumes).
//
// `lower.rs` resolves a source/output/dst LEAF to a device column base; against
// the real fixture every leaf maps through ONE of three companion key-spaces:
//   - `addr_resolve`  (resident input/output/cache-out GKRAddress → ptr),
//   - `cf.cached_alias` (same-layer Cached *Place* → producing cache → cache-out
//     GKRAddress, which is an `addr_resolve` key once the cache has fired),
//   - `scratch_ref`   (ScratchSpace/InnerLayer MaxQuadratic operands).
// `VectorizedLookupSetup` cache outs are NOT bound at a GKRAddress; they live in
// the forward setup's `generic_lookup()` buffer (resolved separately).
// ===========================================================================

/// Is `addr` a witness-stage scratch address (resolved via `scratch_ref`, not
/// `addr_resolve`)? MaxQuadratic operands carry these.
pub(crate) fn is_scratch_addr(addr: GKRAddress) -> bool {
    matches!(
        addr,
        GKRAddress::ScratchSpace(_) | GKRAddress::InnerLayer { .. }
    )
}

/// Look up a `GKRAddress`: `scratch_ref` first (the layer's hydrated scratch
/// values), then the layer's `addr_resolve`, then the POST-CAPTURE `storage` as
/// a fallback. The storage fallback covers a GateOutput source that references a
/// MaxQuadratic output at the NEXT layer (`InnerLayer { layer: L+1 }`), hydrated
/// only when that later layer was captured — resident in `storage` but absent
/// from layer L's per-layer maps. Returns `None` if none carries it.
pub(crate) fn resolve_addr(
    layer: &LayerFixture,
    storage: &GpuGKRStorage<BF, E4>,
    addr: GKRAddress,
) -> Option<*const u8> {
    if is_scratch_addr(addr) {
        if let Some(&(_, p)) = layer.scratch_ref.iter().find(|&&(a, _)| a == addr) {
            return Some(p);
        }
    }
    if let Some(&p) = layer.addr_resolve.get(&addr) {
        return Some(p);
    }
    if let Some(p) = storage.try_get_base_poly(addr) {
        return Some(p.as_ptr() as *const u8);
    }
    storage
        .try_get_ext_poly(addr)
        .map(|p| p.as_ptr() as *const u8)
}

/// Resolve the device base for the cache out of payload `ci` (a `Cached`
/// GKRAddress that is an `addr_resolve` key once the cache has fired).
pub(crate) fn resolve_cache_out(
    layer: &LayerFixture,
    storage: &GpuGKRStorage<BF, E4>,
    cf: &CompiledForward,
    ci: usize,
) -> Option<*const u8> {
    let addr = match &cf.payloads[ci] {
        PayloadRecord::Cache(c) => c.out.1,
        PayloadRecord::Gate(_) => return None,
    };
    resolve_addr(layer, storage, addr)
}

/// The materialized GKRAddress of producer `producer`'s output `out` — the gate
/// `dst[out].addr` (or cache `out.1`). A `GateOutput` source/leaf references a
/// gate whose output production is NOT in the forward program (filtered out as
/// `fwd_eligible`/equal-work, materialized separately into storage); its value
/// is the resident column at that dst address.
fn producer_output_addr(
    layer_ir: &CodegenLayer,
    producer: ProducerId,
    out: u32,
) -> Option<GKRAddress> {
    match producer {
        ProducerId::Gate(g) => layer_ir
            .gates
            .get(g as usize)
            .and_then(|gate| gate.dst.get(out as usize))
            .map(|slot| slot.addr),
        ProducerId::GateExternal(g) => layer_ir
            .gates_external
            .get(g as usize)
            .and_then(|gate| gate.dst.get(out as usize))
            .map(|slot| slot.addr),
        ProducerId::Cache(c) => layer_ir.caches.get(c as usize).map(|cache| cache.out.1),
    }
}

/// Resolve ONE arena leaf node (source/output/dst) to its device column base.
/// Branches on the arena variant + address class per the three-key-space logic.
pub(crate) fn resolve_leaf_node(
    layer: &LayerFixture,
    storage: &GpuGKRStorage<BF, E4>,
    cf: &CompiledForward,
    layer_ir: &CodegenLayer,
    node: usize,
) -> *const u8 {
    match &layer_ir.arena.nodes[node] {
        ExprNode::Place { addr, .. } => {
            // A same-layer Cached Place is an alias to its producing cache's out
            // cell (resolved through cached_alias → cache-out address); a Cached
            // Place with no producer this layer is resident from a prior layer
            // (addr_resolve). Scratch Places resolve via scratch_ref.
            if let Some(&ci) = cf.cached_alias.get(&node) {
                resolve_cache_out(layer, storage, cf, ci as usize).unwrap_or_else(|| {
                    panic!("resolve_leaf: cached alias node {node} (cache {ci}) unresolved")
                })
            } else {
                resolve_addr(layer, storage, *addr).unwrap_or_else(|| {
                    panic!("resolve_leaf: Place node {node} addr {addr:?} unresolved")
                })
            }
        }
        // A GateOutput leaf carries no address on the node. If it aliases a
        // same-layer cache out, resolve through cached_alias; otherwise it is the
        // output of a non-fwd-eligible producer materialized separately into
        // storage — resolve through that producer's dst address (a MaxQuadratic
        // producer's dst at `InnerLayer { layer: L+1 }` resolves to the hydrated
        // scratch value via the storage fallback in `resolve_addr`).
        ExprNode::GateOutput { producer, out, .. } => {
            if let Some(&ci) = cf.cached_alias.get(&node) {
                return resolve_cache_out(layer, storage, cf, ci as usize).unwrap_or_else(|| {
                    panic!("resolve_leaf: GateOutput alias node {node} (cache {ci}) unresolved")
                });
            }
            let addr = producer_output_addr(layer_ir, *producer, *out).unwrap_or_else(|| {
                panic!("resolve_leaf: GateOutput node {node} ({producer:?} out {out}) has no producer dst")
            });
            resolve_addr(layer, storage, addr).unwrap_or_else(|| {
                panic!(
                    "resolve_leaf: GateOutput node {node} ({producer:?}) dst {addr:?} unresolved"
                )
            })
        }
        other => panic!("resolve_leaf: node {node} is not a leaf: {other:?}"),
    }
}

/// Resolve a source-bank index `i` (into `cf.source_map.bf` / `.e4`) to its
/// device column base, mapping the bank index → arena node → leaf resolution.
pub(crate) fn resolve_source(
    layer: &LayerFixture,
    storage: &GpuGKRStorage<BF, E4>,
    cf: &CompiledForward,
    layer_ir: &CodegenLayer,
    i: usize,
    e4: bool,
) -> *const u8 {
    let node = if e4 {
        cf.source_map.e4[i]
    } else {
        cf.source_map.bf[i]
    };
    resolve_leaf_node(layer, storage, cf, layer_ir, node)
}

/// If bf source-bank index `i` is a `VirtualSetup` Place leaf, return its poly
/// kind. Virtual-setup columns have NO resident device buffer (production
/// synthesizes them from the row index inside the kernel via
/// `gkr_virtual_base_value`); the interpreter, which reads a flat pointer per
/// source, needs them MATERIALIZED into a real buffer (see
/// `materialize_virtual_setup_column`). e4 sources are never virtual-setup
/// (virtual setup polys are base-field), so only the bf bank is scanned.
pub(crate) fn source_virtual_setup(
    cf: &CompiledForward,
    arena: &[ExprNode],
    i: usize,
) -> Option<VirtualSetupPoly> {
    let node = cf.source_map.bf[i];
    match arena[node] {
        ExprNode::Place {
            addr: GKRAddress::VirtualSetup(poly),
            ..
        } => Some(poly),
        _ => None,
    }
}

/// Materialize the per-row values of a virtual-setup base column for `t` rows,
/// byte-for-byte equal to the device `gkr_virtual_base_value` switch
/// (`native/prover/gkr/support/kernel_helpers.cuh`). Returned canonical-form
/// `BF` (Montgomery, the device column representation).
pub(crate) fn materialize_virtual_setup_column(poly: VirtualSetupPoly, t: usize) -> Vec<BF> {
    // Mirror of GKR_TIMESTAMP_COLUMNS_NUM_BITS (descriptors.cuh) — sourced from
    // the upstream constant so it cannot drift from the native value.
    let timestamp_bits: u32 = crate::upstream::TIMESTAMP_COLUMNS_NUM_BITS;
    (0..t as u32)
        .map(|row| {
            let v = match poly {
                VirtualSetupPoly::RangeCheck16Bits => {
                    if row < (1u32 << 16) {
                        row
                    } else {
                        0
                    }
                }
                VirtualSetupPoly::RangeCheckTimestamp => {
                    if row < (1u32 << timestamp_bits) {
                        row
                    } else {
                        0
                    }
                }
                VirtualSetupPoly::InitsAndTeardownsLow => (row << 2) & 0xffff,
                VirtualSetupPoly::InitsAndTeardownsHigh => row >> 14,
            };
            BF::from_u32_with_reduction(v)
        })
        .collect()
}

/// Resolve a `cf.outputs` slot `j` (its arena node id is the second tuple field)
/// to a `*mut u8` column base + whether the output column holds e4 elements.
pub(crate) fn resolve_output(
    layer: &LayerFixture,
    storage: &GpuGKRStorage<BF, E4>,
    cf: &CompiledForward,
    layer_ir: &CodegenLayer,
    j: u16,
) -> (*mut u8, bool) {
    let &(_, node) = cf
        .outputs
        .iter()
        .find(|&&(jj, _)| jj == j)
        .unwrap_or_else(|| panic!("resolve_output: unknown output slot {j}"));
    let e4 = matches!(
        layer_ir.arena.nodes[node],
        ExprNode::Place {
            domain: cs::gkr_compiler::codegen_ir::Domain::Ext,
            ..
        } | ExprNode::GateOutput {
            domain: cs::gkr_compiler::codegen_ir::Domain::Ext,
            ..
        }
    );
    (
        resolve_leaf_node(layer, storage, cf, layer_ir, node) as *mut u8,
        e4,
    )
}

/// Resolve the decoder execute-predicate column (a bf column at
/// `BaseLayerMemory(machine_state.execute)`), for decoder vector lookups.
pub(crate) fn resolve_decoder_pred(
    layer: &LayerFixture,
    storage: &GpuGKRStorage<BF, E4>,
    decoder_predicate_address: Option<GKRAddress>,
) -> *const u8 {
    let addr = decoder_predicate_address
        .expect("resolve_decoder_pred: decoder lookup without a machine-state predicate address");
    resolve_addr(layer, storage, addr)
        .unwrap_or_else(|| panic!("resolve_decoder_pred: predicate addr {addr:?} unresolved"))
}
