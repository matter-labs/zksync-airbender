//! Standalone GKR codegen IR for CUDA kernel generation, described in
//! `.agents/specs/2026-06-06-gkr-codegen-expr-ir-design.md`.
//!
//! Purpose: validate the spec's type shapes against the REAL `cs` artifact types,
//! and exercise the core mechanics (NoFieldStructuredExpression -> arena + CSE,
//! MaxQuadFlat mirroring, forward_source/scratch, serde round-trip, verify()).
//!
//! Lowers all 30 `NoFieldGKRRelation` variants into the frozen `GateKind`
//! contract (no `Unhandled` catch-all and no `todo!()` stubs in `lower_relation`).
//!
//! Lowers from an already-compiled artifact (`GKRCircuitArtifact`/
//! `GKRLayerDescription`) — no compiler/prover changes. This confirms the spec's
//! "given a valid compiled GKR artifact, emit a faithful IR" contract is buildable.

use super::{GateArtifacts, GKRLayerDescription, NoFieldGKRRelation, NoFieldStructuredExpression};
use crate::definitions::gkr::{
    NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
};
use crate::definitions::GKRAddress;
use std::collections::{BTreeMap, HashMap};

// ---------------------------------------------------------------------------
// Re-export the source types that CodegenGlobals embeds.
// Confirmed paths (rg verified):
//   OutputType:          crate::definitions::OutputType (re-exported via super as pub use)
//   GKRMemoryLayout:     crate::definitions::gkr::GKRMemoryLayout
//   GKRWitnessLayout:    crate::definitions::gkr::GKRWitnessLayout
// The gkr_compiler/mod.rs already `pub use`s them, so `super::` works.
// ---------------------------------------------------------------------------
use crate::definitions::gkr::{GKRMemoryLayout, GKRWitnessLayout};

use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub struct NodeId(pub u32);

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProducerId {
    Gate(u32),
    GateExternal(u32),
    Cache(u32),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum Domain {
    Base,
    Ext,
}

/// One value node of the shared per-layer DAG. Hash/Eq is the CSE key and INCLUDES
/// `Domain`. `GateOutput`/`Place` are not merged across producers/domains.
#[derive(Clone, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExprNode {
    Constant(u32),
    Place { addr: GKRAddress, domain: Domain },
    GateOutput { producer: ProducerId, out: u32, domain: Domain },
    Sum { terms: Vec<NodeId>, domain: Domain },
    Product { factors: Vec<NodeId>, domain: Domain },
}

impl ExprNode {
    fn domain(&self) -> Domain {
        match self {
            ExprNode::Constant(_) => Domain::Base,
            ExprNode::Place { domain, .. }
            | ExprNode::GateOutput { domain, .. }
            | ExprNode::Sum { domain, .. }
            | ExprNode::Product { domain, .. } => *domain,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeHints {
    pub uses: u32,
    pub footprint: Vec<GKRAddress>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExprArena {
    pub nodes: Vec<ExprNode>,
    pub hints: Vec<NodeHints>,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum ForwardSource {
    Computed,
    ScratchPrefill,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OutputSlot {
    pub node: NodeId,
    pub addr: GKRAddress,
    pub forward_source: ForwardSource,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BatchTerm {
    pub power: u32,
    pub value: NodeId,
}

/// Lowered `NoFieldLinearRelation`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LinearComb {
    pub terms: Vec<(u32, NodeId)>,
    pub constant: u32,
}

/// Lowered `NoFieldMaxQuadraticGKRRelation` (mod.rs:137-141), operands -> NodeId.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MaxQuadFlat {
    pub quadratic: Vec<(NodeId, Vec<(u32, NodeId)>)>,
    pub linear: Vec<(u32, NodeId)>,
    pub constant: u32,
}

// ===========================================================================
// Lowered helper structs for GateKind payloads
// ===========================================================================

/// Lowered NoFieldSingleColumnLookupRelation (lookup.rs:6-11).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SingleColumnLookup {
    pub column: LinearComb,
    pub lookup_set_index: usize,
}

/// Lowered NoFieldVectorLookupRelation (lookup.rs:14-19).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct VectorLookup {
    pub columns: Vec<LinearComb>,
    pub lookup_set_index: usize,
}

/// Field-for-field mirror of NoFieldSpecialMemoryContributionRelation (mod.rs:309-315).
/// The source struct already derives serde, so we embed it verbatim and pair it with
/// the operand NodeIds (its `dependencies()`, all BaseLayerMemory reads).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MemTupleDescriptor {
    pub descriptor: super::NoFieldSpecialMemoryContributionRelation,
    pub operands: Vec<NodeId>,
}

/// Complete GateKind variant contract — all 30 variants, no Unhandled catch-all.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum GateKind {
    LinearBaseField { input: LinearComb },
    MaxQuadratic { flat: MaxQuadFlat, expr: NodeId },
    EnforceSingleMaxQuadraticConstraint { flat: MaxQuadFlat, expr: NodeId },
    EnforceConstraintsMaxQuadratic {
        quadratic: Vec<((NodeId, NodeId), Vec<(u32, usize)>)>,
        linear: Vec<(NodeId, Vec<(u32, usize)>)>,
        constants: Vec<(u32, usize)>,
    },
    CopyInBaseField { input: NodeId },
    CopyInExtensionField { input: NodeId },
    InitialGrandProductFromCaches { input: [NodeId; 2] },
    InitialGrandProductWithoutCaches { input: [MemTupleDescriptor; 2] },
    UnbalancedGrandProductWithCache { scalar: NodeId, input: NodeId },
    MaterializeGrandProductTermExpression { input: MemTupleDescriptor },
    TrivialProduct { input: [NodeId; 2] },
    MaskIntoIdentityProduct { input: NodeId, mask: NodeId },
    MaterializeSingleLookupInput { input: SingleColumnLookup, range_check_width: u32 },
    MaterializedVectorLookupInput { input: VectorLookup },
    LookupWithCachedDensAndSetup { input: [NodeId; 2], setup: [NodeId; 2] },
    LookupWithDensAndSetupExpressions {
        input_addr: NodeId,
        input_vec: VectorLookup,
        setup_addr: NodeId,
        setup_extra: Vec<NodeId>,
    },
    LookupWithDensAndCachedSetup {
        input_addr: NodeId,
        input_vec: VectorLookup,
        setup: [NodeId; 2],
    },
    LookupPairFromBaseInputs { input: [SingleColumnLookup; 2], range_check_width: u32 },
    LookupPairFromMaterializedBaseInputs { input: [NodeId; 2] },
    LookupFromMaterializedBaseInputWithSetup { input: NodeId, setup: [NodeId; 2] },
    LookupUnbalancedPairWithMaterializedBaseInputs { input: [NodeId; 2], remainder: NodeId },
    LookupPairFromVectorInputs { input: [VectorLookup; 2] },
    LookupPairFromMaterializedVectorInputs { input: [NodeId; 2] },
    LookupFromVectorInputWithSetup { input: VectorLookup, setup_addr: NodeId, setup_extra: Vec<NodeId> },
    LookupFromMaterializedVectorInputWithSetup { input: NodeId, setup: [NodeId; 2] },
    LookupPairFromCachedVectorInputs { input: [NodeId; 2] },
    LookupUnbalancedPairWithVectorInputs { input: [NodeId; 2], remainder: VectorLookup },
    LookupUnbalancedPairWithMaterializedVectorInputs { input: [NodeId; 2], remainder: NodeId },
    AggregateLookupRationalPair { input: [[NodeId; 2]; 2] },
    InitsOrTeardownsInitialPair {
        timestamp_and_value: super::InitsOrTeardownsTimestampAndValue,
        setup: [NodeId; 2],
        set_idxes: [usize; 2],
    },
}

// ===========================================================================
// Cache types
// ===========================================================================

/// One cache entry in the per-layer IR.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum CacheKind {
    SingleColumnLookup { column: LinearComb, lookup_set_index: usize, range_check_width: usize },
    VectorizedLookup { columns: Vec<LinearComb>, lookup_set_index: usize },
    MemoryTuple { descriptor: MemTupleDescriptor },
    VectorizedLookupSetup,
}

/// Lowered cache entry with its inputs and output node + address.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CodegenCache {
    pub kind: CacheKind,
    pub inputs: Vec<NodeId>,
    pub out: (NodeId, GKRAddress),
}

// ===========================================================================
// Circuit-level globals
// ===========================================================================

/// All circuit-wide constants from `GKRCircuitArtifact` that the CUDA kernel
/// generator needs but are not per-layer. Mirrors the artifact's scalar fields;
/// field-generic and compiler-internal fields (degree-N constraints, placement_data,
/// variable_names, aux_layout_data) are excluded as they are not kernel inputs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodegenGlobals {
    pub trace_len: usize,
    pub offset_for_decoder_table: usize,
    pub has_decoder_lookup: bool,
    pub generic_lookup_tables_width: usize,
    pub tables_ids_in_generic_lookups: bool,
    pub num_generic_lookups: usize,
    pub decode_table_columns_mask: Vec<bool>,
    pub table_offsets: Vec<u32>,
    pub total_tables_size: usize,
    pub scratch_space_size: usize,
    pub scratch_space_mapping: BTreeMap<GKRAddress, usize>,
    pub scratch_space_mapping_rev: BTreeMap<usize, GKRAddress>,
    pub global_output_map: BTreeMap<super::OutputType, Vec<GKRAddress>>,
    pub memory_layout: GKRMemoryLayout,
    pub witness_layout: GKRWitnessLayout,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodegenGate {
    pub kind: GateKind,
    pub dst: Vec<OutputSlot>,
    pub batch_terms: Vec<BatchTerm>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodegenLayer {
    pub arena: ExprArena,
    pub gates_external: Vec<CodegenGate>,
    pub gates: Vec<CodegenGate>,
    pub caches: Vec<CodegenCache>,
    pub intermediate_layer_width: Option<usize>,
}

/// The top-level serializable IR for an entire GKR circuit — all layers plus globals.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodegenCircuit {
    pub layers: Vec<CodegenLayer>,
    pub globals: CodegenGlobals,
}

// ===========================================================================
// Build pass
// ===========================================================================

#[derive(Default)]
struct ArenaBuilder {
    nodes: Vec<ExprNode>,
    intern: HashMap<ExprNode, NodeId>,
    /// Intra-layer addresses written by a gate/cache output -> producing GateOutput
    /// NodeId. A same-layer consumer resolves through this BEFORE a Place fallback,
    /// so producer->consumer is an explicit arena edge (spec Round-10 / finding 6).
    produced: HashMap<GKRAddress, NodeId>,
}

impl ArenaBuilder {
    fn intern(&mut self, node: ExprNode) -> NodeId {
        if let Some(&id) = self.intern.get(&node) {
            return id;
        }
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(node.clone());
        self.intern.insert(node, id);
        id
    }

    /// GateOutput nodes are unique per production — never interned. If `addr` is an
    /// intra-layer producible address (InnerLayer/Cached), record it in `produced`
    /// so later same-layer consumers `resolve()` to this node.
    fn add_gate_output(
        &mut self,
        producer: ProducerId,
        out: u32,
        domain: Domain,
        addr: GKRAddress,
    ) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(ExprNode::GateOutput {
            producer,
            out,
            domain,
        });
        if matches!(addr, GKRAddress::InnerLayer { .. } | GKRAddress::Cached { .. }) {
            self.produced.insert(addr, id);
        }
        id
    }

    fn place(&mut self, addr: GKRAddress, domain: Domain) -> NodeId {
        self.intern(ExprNode::Place { addr, domain })
    }

    /// Resolve an operand address: an intra-layer address already produced this layer
    /// -> its GateOutput NodeId (explicit edge); otherwise a `Place` leaf.
    fn resolve(&mut self, addr: GKRAddress, domain: Domain) -> NodeId {
        if let Some(&id) = self.produced.get(&addr) {
            return id;
        }
        self.place(addr, domain)
    }

    /// Lower a `NoFieldStructuredExpression` into the arena, canonically sorting
    /// commutative children so structurally-equal subexpressions dedup.
    fn lower_expr(&mut self, e: &NoFieldStructuredExpression, domain: Domain) -> NodeId {
        match e {
            NoFieldStructuredExpression::Constant(c) => self.intern(ExprNode::Constant(*c)),
            NoFieldStructuredExpression::Place(addr) => self.resolve(*addr, domain),
            NoFieldStructuredExpression::Sum(children) => {
                let mut terms: Vec<NodeId> =
                    children.iter().map(|c| self.lower_expr(c, domain)).collect();
                terms.sort_by_key(|n| n.0);
                self.intern(ExprNode::Sum { terms, domain })
            }
            NoFieldStructuredExpression::Product(children) => {
                let mut factors: Vec<NodeId> =
                    children.iter().map(|c| self.lower_expr(c, domain)).collect();
                factors.sort_by_key(|n| n.0);
                self.intern(ExprNode::Product { factors, domain })
            }
        }
    }

    fn lower_linear(&mut self, lin: &NoFieldLinearRelation, domain: Domain) -> LinearComb {
        let terms = lin
            .linear_terms
            .iter()
            .map(|(c, addr)| (*c, self.resolve(*addr, domain)))
            .collect();
        LinearComb {
            terms,
            constant: lin.constant,
        }
    }
}

fn forward_source_for(
    output: &GKRAddress,
    is_max_quadratic: bool,
    scratch: &BTreeMap<GKRAddress, usize>,
) -> ForwardSource {
    // EXACT prover rule (not raw membership): only MaxQuadratic is scratch-skipped.
    if is_max_quadratic && scratch.contains_key(output) {
        ForwardSource::ScratchPrefill
    } else {
        ForwardSource::Computed
    }
}

/// Lower a single relation into a `CodegenGate` (batch powers assigned later).
fn lower_relation(
    b: &mut ArenaBuilder,
    rel: &NoFieldGKRRelation,
    producer: ProducerId,
    scratch: &BTreeMap<GKRAddress, usize>,
) -> CodegenGate {
    use NoFieldGKRRelation as R;
    let (kind, dst): (GateKind, Vec<OutputSlot>) = match rel {
        R::LinearBaseFieldRelation { input, output } => {
            let lc = b.lower_linear(input, Domain::Base);
            let node = b.add_gate_output(producer, 0, Domain::Base, *output);
            (
                GateKind::LinearBaseField { input: lc },
                vec![OutputSlot {
                    node,
                    addr: *output,
                    forward_source: ForwardSource::Computed,
                }],
            )
        }
        R::MaxQuadratic {
            input,
            expression,
            output,
        } => {
            let domain = relation_metadata(rel).out_domain;
            debug_assert!(matches!(domain, Domain::Base), "MaxQuadratic is always base-field");
            let flat = lower_max_quad_flat(b, input, domain);
            let expr = b.lower_expr(expression, domain);
            let node = b.add_gate_output(producer, 0, domain, *output);
            (
                GateKind::MaxQuadratic { flat, expr },
                vec![OutputSlot {
                    node,
                    addr: *output,
                    forward_source: forward_source_for(output, true, scratch),
                }],
            )
        }
        R::EnforceSingleMaxQuadraticConstraint { input, expression } => {
            let domain = relation_metadata(rel).out_domain;
            debug_assert!(matches!(domain, Domain::Base), "EnforceSingleMaxQuadraticConstraint is always base-field");
            let flat = lower_max_quad_flat(b, input, domain);
            let expr = b.lower_expr(expression, domain);
            (
                GateKind::EnforceSingleMaxQuadraticConstraint { flat, expr },
                vec![],
            )
        }
        R::EnforceConstraintsMaxQuadratic { input } => {
            let domain = relation_metadata(rel).out_domain;
            debug_assert!(matches!(domain, Domain::Base), "EnforceConstraintsMaxQuadratic is always base-field");
            let quadratic = input
                .quadratic_terms
                .iter()
                .map(|((a, c), powers)| {
                    let an = b.resolve(*a, domain);
                    let cn = b.resolve(*c, domain);
                    ((an, cn), powers.to_vec())
                })
                .collect();
            let linear = input
                .linear_terms
                .iter()
                .map(|(a, powers)| (b.resolve(*a, domain), powers.to_vec()))
                .collect();
            let constants = input.constants.to_vec();
            (
                GateKind::EnforceConstraintsMaxQuadratic {
                    quadratic,
                    linear,
                    constants,
                },
                vec![],
            )
        }
        R::CopyInBaseField { input, output } => {
            let domain = relation_metadata(rel).out_domain;
            let inode = b.resolve(*input, domain);
            let node = b.add_gate_output(producer, 0, domain, *output);
            (
                GateKind::CopyInBaseField { input: inode },
                vec![OutputSlot {
                    node,
                    addr: *output,
                    forward_source: ForwardSource::Computed,
                }],
            )
        }
        R::CopyInExtensionField { input, output } => {
            let domain = relation_metadata(rel).out_domain;
            let inode = b.resolve(*input, domain);
            let node = b.add_gate_output(producer, 0, domain, *output);
            (
                GateKind::CopyInExtensionField { input: inode },
                vec![OutputSlot {
                    node,
                    addr: *output,
                    forward_source: ForwardSource::Computed,
                }],
            )
        }
        // --- grand-product / product family (Task 4) ---
        R::InitialGrandProductFromCaches { input, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (GateKind::InitialGrandProductFromCaches { input: i }, one_out(node, *output, scratch, false))
        }
        R::InitialGrandProductWithoutCaches { input, output } => {
            let d = [lower_mem_tuple(b, &input[0]), lower_mem_tuple(b, &input[1])];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (GateKind::InitialGrandProductWithoutCaches { input: d }, one_out(node, *output, scratch, false))
        }
        R::UnbalancedGrandProductWithCache { scalar, input, output } => {
            let s = b.resolve(*scalar, Domain::Ext);
            let i = b.resolve(*input, Domain::Ext);
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (GateKind::UnbalancedGrandProductWithCache { scalar: s, input: i }, one_out(node, *output, scratch, false))
        }
        R::MaterializeGrandProductTermExpression { input, output } => {
            let d = lower_mem_tuple(b, input);
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (GateKind::MaterializeGrandProductTermExpression { input: d }, one_out(node, *output, scratch, false))
        }
        R::TrivialProduct { input, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (GateKind::TrivialProduct { input: i }, one_out(node, *output, scratch, false))
        }
        R::MaskIntoIdentityProduct { input, mask, output } => {
            // MIXED: mask is Base-field, input is extension-field (mask_into_identity add_base_by_ext).
            let m = b.resolve(*mask, Domain::Base);
            let i = b.resolve(*input, Domain::Ext);
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (GateKind::MaskIntoIdentityProduct { input: i, mask: m }, one_out(node, *output, scratch, false))
        }
        R::MaterializeSingleLookupInput { input, output, range_check_width } => {
            let s = lower_single_col(b, input, Domain::Base);
            let node = b.add_gate_output(producer, 0, Domain::Base, *output);
            (
                GateKind::MaterializeSingleLookupInput { input: s, range_check_width: *range_check_width },
                one_out(node, *output, scratch, false),
            )
        }
        R::MaterializedVectorLookupInput { input, output } => {
            let v = lower_vector(b, input, Domain::Base); // base-field columns, ext-field result
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::MaterializedVectorLookupInput { input: v },
                one_out(node, *output, scratch, false),
            )
        }
        R::LookupWithCachedDensAndSetup { input, setup, output } => {
            let i = [b.resolve(input[0], Domain::Base), b.resolve(input[1], Domain::Ext)];
            let s = [b.resolve(setup[0], Domain::Base), b.resolve(setup[1], Domain::Ext)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupWithCachedDensAndSetup { input: i, setup: s }, dst)
        }
        R::LookupWithDensAndSetupExpressions { input, setup, output } => {
            let input_addr = b.resolve(input.0, Domain::Ext);
            let input_vec = lower_vector(b, &input.1, Domain::Base);
            let setup_addr = b.resolve(setup.0, Domain::Ext);
            let setup_extra = setup.1.iter().map(|a| b.resolve(*a, Domain::Ext)).collect();
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupWithDensAndSetupExpressions { input_addr, input_vec, setup_addr, setup_extra }, dst)
        }
        R::LookupWithDensAndCachedSetup { input, setup, output } => {
            let input_addr = b.resolve(input.0, Domain::Ext);
            let input_vec = lower_vector(b, &input.1, Domain::Base);
            let s = [b.resolve(setup.0, Domain::Ext), b.resolve(setup.1, Domain::Ext)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupWithDensAndCachedSetup { input_addr, input_vec, setup: s }, dst)
        }
        R::LookupPairFromBaseInputs { input, output, range_check_width } => {
            let i = [lower_single_col(b, &input[0], Domain::Base), lower_single_col(b, &input[1], Domain::Base)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromBaseInputs { input: i, range_check_width: *range_check_width }, dst)
        }
        R::LookupPairFromMaterializedBaseInputs { input, output } => {
            let i = [b.resolve(input[0], Domain::Base), b.resolve(input[1], Domain::Base)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromMaterializedBaseInputs { input: i }, dst)
        }
        R::LookupFromMaterializedBaseInputWithSetup { input, setup, output } => {
            let i = b.resolve(*input, Domain::Base);
            let s = [b.resolve(setup[0], Domain::Base), b.resolve(setup[1], Domain::Base)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupFromMaterializedBaseInputWithSetup { input: i, setup: s }, dst)
        }
        R::LookupUnbalancedPairWithMaterializedBaseInputs { input, remainder, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let r = b.resolve(*remainder, Domain::Base);
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupUnbalancedPairWithMaterializedBaseInputs { input: i, remainder: r }, dst)
        }
        R::LookupPairFromVectorInputs { input, output } => {
            let i = [lower_vector(b, &input[0], Domain::Base), lower_vector(b, &input[1], Domain::Base)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromVectorInputs { input: i }, dst)
        }
        R::LookupPairFromMaterializedVectorInputs { input, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromMaterializedVectorInputs { input: i }, dst)
        }
        R::LookupFromVectorInputWithSetup { input, setup, output } => {
            let v = lower_vector(b, input, Domain::Base);
            let setup_addr = b.resolve(setup.0, Domain::Ext);
            let setup_extra = setup.1.iter().map(|a| b.resolve(*a, Domain::Ext)).collect();
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupFromVectorInputWithSetup { input: v, setup_addr, setup_extra }, dst)
        }
        R::LookupFromMaterializedVectorInputWithSetup { input, setup, output } => {
            let i = b.resolve(*input, Domain::Ext);
            let s = [b.resolve(setup[0], Domain::Base), b.resolve(setup[1], Domain::Ext)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupFromMaterializedVectorInputWithSetup { input: i, setup: s }, dst)
        }
        R::LookupPairFromCachedVectorInputs { input, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromCachedVectorInputs { input: i }, dst)
        }
        R::LookupUnbalancedPairWithVectorInputs { input, remainder, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let r = lower_vector(b, remainder, Domain::Base);
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupUnbalancedPairWithVectorInputs { input: i, remainder: r }, dst)
        }
        R::LookupUnbalancedPairWithMaterializedVectorInputs { input, remainder, output } => {
            let i = [b.resolve(input[0], Domain::Ext), b.resolve(input[1], Domain::Ext)];
            let r = b.resolve(*remainder, Domain::Ext);
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupUnbalancedPairWithMaterializedVectorInputs { input: i, remainder: r }, dst)
        }
        R::AggregateLookupRationalPair { input, output } => {
            let i = [
                [b.resolve(input[0][0], Domain::Ext), b.resolve(input[0][1], Domain::Ext)],
                [b.resolve(input[1][0], Domain::Ext), b.resolve(input[1][1], Domain::Ext)],
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::AggregateLookupRationalPair { input: i }, dst)
        }
        R::InitsOrTeardownsInitialPair { timestamp_and_value, setup, output, set_idxes } => {
            // setup BASE, result Ext.
            let s = [b.resolve(setup[0], Domain::Base), b.resolve(setup[1], Domain::Base)];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::InitsOrTeardownsInitialPair {
                    timestamp_and_value: timestamp_and_value.clone(),
                    setup: s,
                    set_idxes: *set_idxes,
                },
                one_out(node, *output, scratch, false),
            )
        }
    };
    CodegenGate {
        kind,
        dst,
        batch_terms: vec![],
    }
}

// ---------------------------------------------------------------------------
// Task 4 helpers
// ---------------------------------------------------------------------------

/// Build a single-slot `dst` vec for a gate with one output.
fn one_out(
    node: NodeId,
    addr: GKRAddress,
    scratch: &BTreeMap<GKRAddress, usize>,
    is_max_quad: bool,
) -> Vec<OutputSlot> {
    vec![OutputSlot {
        node,
        addr,
        forward_source: forward_source_for(&addr, is_max_quad, scratch),
    }]
}

/// Build a two-slot `dst` vec for a gate with two outputs (the (num, den) lookup pair).
fn two_out(
    b: &mut ArenaBuilder,
    producer: ProducerId,
    out: &[GKRAddress; 2],
    d: Domain,
    scratch: &BTreeMap<GKRAddress, usize>,
) -> Vec<OutputSlot> {
    let n0 = b.add_gate_output(producer, 0, d, out[0]);
    let n1 = b.add_gate_output(producer, 1, d, out[1]);
    vec![
        OutputSlot { node: n0, addr: out[0], forward_source: forward_source_for(&out[0], false, scratch) },
        OutputSlot { node: n1, addr: out[1], forward_source: forward_source_for(&out[1], false, scratch) },
    ]
}

/// Lower a `NoFieldSpecialMemoryContributionRelation` by resolving each of its
/// `dependencies()` (all `BaseLayerMemory` reads) as Base-domain Place nodes.
fn lower_mem_tuple(
    b: &mut ArenaBuilder,
    m: &super::NoFieldSpecialMemoryContributionRelation,
) -> MemTupleDescriptor {
    let operands = m.dependencies().into_iter().map(|a| b.resolve(a, Domain::Base)).collect();
    MemTupleDescriptor {
        descriptor: m.clone(),
        operands,
    }
}

/// Lower a `NoFieldSingleColumnLookupRelation` into the arena.
fn lower_single_col(
    b: &mut ArenaBuilder,
    r: &NoFieldSingleColumnLookupRelation,
    d: Domain,
) -> SingleColumnLookup {
    SingleColumnLookup {
        column: b.lower_linear(&r.input, d),
        lookup_set_index: r.lookup_set_index,
    }
}

/// Lower a `NoFieldVectorLookupRelation` into the arena.
/// `columns` is `Box<[NoFieldLinearRelation]>` in the source type.
fn lower_vector(b: &mut ArenaBuilder, r: &NoFieldVectorLookupRelation, d: Domain) -> VectorLookup {
    VectorLookup {
        columns: r.columns.iter().map(|c| b.lower_linear(c, d)).collect(),
        lookup_set_index: r.lookup_set_index,
    }
}

fn lower_max_quad_flat(
    b: &mut ArenaBuilder,
    input: &super::NoFieldMaxQuadraticGKRRelation,
    domain: Domain,
) -> MaxQuadFlat {
    debug_assert!(matches!(domain, Domain::Base), "lower_max_quad_flat operands are always base-field");
    let quadratic = input
        .quadratic_terms
        .iter()
        .map(|(a, terms)| {
            let an = b.resolve(*a, domain);
            let lowered = terms
                .iter()
                .map(|(c, bb)| (*c, b.resolve(*bb, domain)))
                .collect();
            (an, lowered)
        })
        .collect();
    let linear = input
        .linear_terms
        .iter()
        .map(|(c, a)| (*c, b.resolve(*a, domain)))
        .collect();
    MaxQuadFlat {
        quadratic,
        linear,
        constant: input.constant,
    }
}

/// Assign absolute batch powers over `gates` chained with `gates_external` (caches
/// excluded), one per consumed challenge. The spike uses #challenges = 1 + extra for
/// each emitted output slot beyond the first (a stand-in for the kernel's
/// `num_challenges()`); the real count is validated against the prover in the plan.
fn assign_batch_powers(gates: &mut [CodegenGate], gates_external: &mut [CodegenGate], start: &mut u32) {
    for gate in gates.iter_mut().chain(gates_external.iter_mut()) {
        let n_challenges = num_challenges_stub(gate);
        let mut terms = Vec::with_capacity(n_challenges as usize);
        // value weighted: each output's node, or (no-output) any constant proxy.
        let value = gate
            .dst
            .first()
            .map(|o| o.node)
            .unwrap_or(NodeId(0));
        for _ in 0..n_challenges {
            terms.push(BatchTerm {
                power: *start,
                value,
            });
            *start += 1;
        }
        gate.batch_terms = terms;
    }
}

fn num_challenges_stub(gate: &CodegenGate) -> u32 {
    // Stand-in: 2 for two-output gates, else 1. Real value = kernel num_challenges().
    if gate.dst.len() == 2 {
        2
    } else {
        1
    }
}

/// Lower one layer. Public so tests can exercise it without a full artifact.
pub fn lower_layer(
    layer: &GKRLayerDescription,
    scratch: &BTreeMap<GKRAddress, usize>,
) -> CodegenLayer {
    let mut b = ArenaBuilder::default();

    let lower_group = |b: &mut ArenaBuilder,
                       group: &[GateArtifacts],
                       producer_of: &dyn Fn(u32) -> ProducerId|
     -> Vec<CodegenGate> {
        group
            .iter()
            .enumerate()
            .map(|(i, g)| lower_relation(b, &g.enforced_relation, producer_of(i as u32), scratch))
            .collect()
    };

    let mut gates = lower_group(&mut b, &layer.gates, &ProducerId::Gate);
    let mut gates_external = lower_group(
        &mut b,
        &layer.gates_with_external_connections,
        &ProducerId::GateExternal,
    );

    let mut power = 0u32;
    assign_batch_powers(&mut gates, &mut gates_external, &mut power);

    let hints = compute_hints(&b.nodes);
    CodegenLayer {
        arena: ExprArena {
            nodes: b.nodes,
            hints,
        },
        gates_external,
        gates,
        caches: vec![], // cache lowering is Task 5+
        intermediate_layer_width: layer.intermediate_layer_width,
    }
}

/// One forward pass over arena order. ScratchPrefill GateOutputs are not produced by
/// the spike's families with forward in-edges, so GateOutput footprint = {} here
/// (full Computed-case union over producer inputs is plan work — see spec).
fn compute_hints(nodes: &[ExprNode]) -> Vec<NodeHints> {
    let mut footprints: Vec<Vec<GKRAddress>> = Vec::with_capacity(nodes.len());
    let mut uses = vec![0u32; nodes.len()];
    for node in nodes.iter() {
        let fp: Vec<GKRAddress> = match node {
            ExprNode::Constant(_) => vec![],
            ExprNode::Place { addr, .. } => vec![*addr],
            ExprNode::GateOutput { .. } => vec![],
            ExprNode::Sum { terms, .. } => union_children(&footprints, terms, &mut uses),
            ExprNode::Product { factors, .. } => union_children(&footprints, factors, &mut uses),
        };
        footprints.push(fp);
    }
    footprints
        .into_iter()
        .zip(uses)
        .map(|(footprint, uses)| NodeHints { uses, footprint })
        .collect()
}

fn union_children(
    footprints: &[Vec<GKRAddress>],
    children: &[NodeId],
    uses: &mut [u32],
) -> Vec<GKRAddress> {
    let mut out: Vec<GKRAddress> = Vec::new();
    for c in children {
        uses[c.0 as usize] += 1;
        out.extend_from_slice(&footprints[c.0 as usize]);
    }
    out.sort(); // GKRAddress derives Ord
    out.dedup();
    out
}

// ===========================================================================
// Per-variant metadata table (Task 2)
// ===========================================================================

/// Per-variant static metadata: how many outputs, how many challenges, and
/// what domain the result lives in. `out_domain` is the RESULT domain only —
/// per-operand domains are mixed (e.g. `MaskIntoIdentityProduct.mask` is Base
/// even though `out_domain = Ext`) and are resolved from each kernel's
/// `GKRInputs` during lowering (Tasks 4-6). Single in-`cs` source of truth,
/// cross-validated against `NoFieldGKRRelation::num_challenges()`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationMeta {
    pub outputs: u8,
    pub num_challenges: u8,
    pub out_domain: Domain,
}

/// Return static metadata for any `NoFieldGKRRelation` variant.
/// The match is exhaustive with NO `_` arm so a future variant breaks the build.
pub fn relation_metadata(rel: &NoFieldGKRRelation) -> RelationMeta {
    use NoFieldGKRRelation as R;
    let (outputs, num_challenges, out_domain) = match rel {
        // -- single-output base-field family --
        R::LinearBaseFieldRelation { .. } => (1, 1, Domain::Base),
        R::MaxQuadratic { .. } => (1, 1, Domain::Base),
        R::EnforceSingleMaxQuadraticConstraint { .. } => (0, 1, Domain::Base),
        R::EnforceConstraintsMaxQuadratic { .. } => (0, 1, Domain::Base),
        R::CopyInBaseField { .. } => (1, 1, Domain::Base),
        // -- single-output extension-field family --
        R::CopyInExtensionField { .. } => (1, 1, Domain::Ext),
        R::InitialGrandProductFromCaches { .. } => (1, 1, Domain::Ext),
        R::InitialGrandProductWithoutCaches { .. } => (1, 1, Domain::Ext),
        R::UnbalancedGrandProductWithCache { .. } => (1, 1, Domain::Ext),
        R::MaterializeGrandProductTermExpression { .. } => (1, 1, Domain::Ext),
        R::TrivialProduct { .. } => (1, 1, Domain::Ext),
        R::MaskIntoIdentityProduct { .. } => (1, 1, Domain::Ext),
        // -- single-output lookup materialization --
        R::MaterializeSingleLookupInput { .. } => (1, 1, Domain::Base),
        R::MaterializedVectorLookupInput { .. } => (1, 1, Domain::Ext),
        // -- two-output (num, den) lookup family --
        R::LookupWithCachedDensAndSetup { .. } => (2, 2, Domain::Ext),
        R::LookupWithDensAndSetupExpressions { .. } => (2, 2, Domain::Ext),
        R::LookupWithDensAndCachedSetup { .. } => (2, 2, Domain::Ext),
        R::LookupPairFromBaseInputs { .. } => (2, 2, Domain::Ext),
        R::LookupPairFromMaterializedBaseInputs { .. } => (2, 2, Domain::Ext),
        R::LookupFromMaterializedBaseInputWithSetup { .. } => (2, 2, Domain::Ext),
        R::LookupUnbalancedPairWithMaterializedBaseInputs { .. } => (2, 2, Domain::Ext),
        R::LookupPairFromVectorInputs { .. } => (2, 2, Domain::Ext),
        R::LookupPairFromMaterializedVectorInputs { .. } => (2, 2, Domain::Ext),
        R::LookupFromVectorInputWithSetup { .. } => (2, 2, Domain::Ext),
        R::LookupFromMaterializedVectorInputWithSetup { .. } => (2, 2, Domain::Ext),
        R::LookupPairFromCachedVectorInputs { .. } => (2, 2, Domain::Ext),
        R::LookupUnbalancedPairWithVectorInputs { .. } => (2, 2, Domain::Ext),
        R::LookupUnbalancedPairWithMaterializedVectorInputs { .. } => (2, 2, Domain::Ext),
        R::AggregateLookupRationalPair { .. } => (2, 2, Domain::Ext),
        // -- inits/teardowns --
        R::InitsOrTeardownsInitialPair { .. } => (1, 1, Domain::Ext),
    };
    RelationMeta { outputs, num_challenges, out_domain }
}

// ===========================================================================
// Validation
// ===========================================================================

impl CodegenLayer {
    /// Subset of the spec's invariants reachable by the spike.
    pub fn verify(&self) -> Result<(), String> {
        let n = self.arena.nodes.len();
        if self.arena.hints.len() != n {
            return Err(format!("hints len {} != nodes len {}", self.arena.hints.len(), n));
        }
        // Strictly forward-referencing arena (topological): node i references only j < i.
        for (i, node) in self.arena.nodes.iter().enumerate() {
            let check = |id: &NodeId| -> Result<(), String> {
                if (id.0 as usize) >= i {
                    return Err(format!("node {} references non-earlier node {}", i, id.0));
                }
                Ok(())
            };
            match node {
                ExprNode::Sum { terms, domain } => {
                    for t in terms {
                        check(t)?;
                        if self.arena.nodes[t.0 as usize].domain() != *domain {
                            return Err(format!("Sum node {} domain disagrees with operand", i));
                        }
                    }
                }
                ExprNode::Product { factors, domain } => {
                    for f in factors {
                        check(f)?;
                        if self.arena.nodes[f.0 as usize].domain() != *domain {
                            return Err(format!("Product node {} domain disagrees with operand", i));
                        }
                    }
                }
                _ => {}
            }
        }
        // Every referenced NodeId in range; ScratchPrefill outputs only on MaxQuadratic.
        for gate in self.gates.iter().chain(self.gates_external.iter()) {
            for slot in &gate.dst {
                if (slot.node.0 as usize) >= n {
                    return Err(format!("dst node {} out of range", slot.node.0));
                }
                if matches!(slot.forward_source, ForwardSource::ScratchPrefill)
                    && !matches!(gate.kind, GateKind::MaxQuadratic { .. })
                {
                    return Err("ScratchPrefill on a non-MaxQuadratic output".to_string());
                }
            }
            for t in &gate.batch_terms {
                if (t.value.0 as usize) >= n {
                    return Err(format!("batch_term value {} out of range", t.value.0));
                }
            }
        }
        // Batch coverage: powers over gates + gates_external are exactly 0..total.
        let mut powers: Vec<u32> = self
            .gates
            .iter()
            .chain(self.gates_external.iter())
            .flat_map(|g| g.batch_terms.iter().map(|t| t.power))
            .collect();
        powers.sort_unstable();
        for (expected, got) in powers.iter().enumerate() {
            if *got != expected as u32 {
                return Err(format!("batch power gap/collision: expected {}, got {}", expected, got));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn blw(i: usize) -> GKRAddress {
        GKRAddress::BaseLayerWitness(i)
    }
    fn inner(layer: usize, offset: usize) -> GKRAddress {
        GKRAddress::InnerLayer { layer, offset }
    }

    /// One constructed value per GateKind variant (NodeId(0) placeholders, empty
    /// Vecs, minimal embedded structs). Used only for type / serde validation.
    fn gatekind_samples() -> Vec<GateKind> {
        use super::super::{
            CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
            InitsOrTeardownsTimestampAndValue, NoFieldSpecialMemoryContributionRelation,
        };
        use crate::definitions::gkr::RamWordRepresentation;

        let n = NodeId(0);
        let lc = LinearComb { terms: vec![], constant: 0 };
        let mq_flat = MaxQuadFlat { quadratic: vec![], linear: vec![], constant: 0 };

        // A minimal NoFieldSpecialMemoryContributionRelation with all-constant fields
        // so it never touches any BaseLayerMemory addresses.
        let mem_desc = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::Constant(0),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let mem_tuple = MemTupleDescriptor { descriptor: mem_desc, operands: vec![] };
        let scl = SingleColumnLookup { column: lc.clone(), lookup_set_index: 0 };
        let vl = VectorLookup { columns: vec![], lookup_set_index: 0 };

        vec![
            // 1
            GateKind::LinearBaseField { input: lc.clone() },
            // 2
            GateKind::MaxQuadratic { flat: mq_flat.clone(), expr: n },
            // 3
            GateKind::EnforceSingleMaxQuadraticConstraint { flat: mq_flat.clone(), expr: n },
            // 4
            GateKind::EnforceConstraintsMaxQuadratic {
                quadratic: vec![],
                linear: vec![],
                constants: vec![],
            },
            // 5
            GateKind::CopyInBaseField { input: n },
            // 6
            GateKind::CopyInExtensionField { input: n },
            // 7
            GateKind::InitialGrandProductFromCaches { input: [n; 2] },
            // 8
            GateKind::InitialGrandProductWithoutCaches {
                input: [mem_tuple.clone(), mem_tuple.clone()],
            },
            // 9
            GateKind::UnbalancedGrandProductWithCache { scalar: n, input: n },
            // 10
            GateKind::MaterializeGrandProductTermExpression { input: mem_tuple.clone() },
            // 11
            GateKind::TrivialProduct { input: [n; 2] },
            // 12
            GateKind::MaskIntoIdentityProduct { input: n, mask: n },
            // 13
            GateKind::MaterializeSingleLookupInput {
                input: scl.clone(),
                range_check_width: 16,
            },
            // 14
            GateKind::MaterializedVectorLookupInput { input: vl.clone() },
            // 15
            GateKind::LookupWithCachedDensAndSetup { input: [n; 2], setup: [n; 2] },
            // 16
            GateKind::LookupWithDensAndSetupExpressions {
                input_addr: n,
                input_vec: vl.clone(),
                setup_addr: n,
                setup_extra: vec![],
            },
            // 17
            GateKind::LookupWithDensAndCachedSetup {
                input_addr: n,
                input_vec: vl.clone(),
                setup: [n; 2],
            },
            // 18
            GateKind::LookupPairFromBaseInputs {
                input: [scl.clone(), scl.clone()],
                range_check_width: 16,
            },
            // 19
            GateKind::LookupPairFromMaterializedBaseInputs { input: [n; 2] },
            // 20
            GateKind::LookupFromMaterializedBaseInputWithSetup { input: n, setup: [n; 2] },
            // 21
            GateKind::LookupUnbalancedPairWithMaterializedBaseInputs {
                input: [n; 2],
                remainder: n,
            },
            // 22
            GateKind::LookupPairFromVectorInputs { input: [vl.clone(), vl.clone()] },
            // 23
            GateKind::LookupPairFromMaterializedVectorInputs { input: [n; 2] },
            // 24
            GateKind::LookupFromVectorInputWithSetup {
                input: vl.clone(),
                setup_addr: n,
                setup_extra: vec![],
            },
            // 25
            GateKind::LookupFromMaterializedVectorInputWithSetup { input: n, setup: [n; 2] },
            // 26
            GateKind::LookupPairFromCachedVectorInputs { input: [n; 2] },
            // 27
            GateKind::LookupUnbalancedPairWithVectorInputs {
                input: [n; 2],
                remainder: vl.clone(),
            },
            // 28
            GateKind::LookupUnbalancedPairWithMaterializedVectorInputs {
                input: [n; 2],
                remainder: n,
            },
            // 29
            GateKind::AggregateLookupRationalPair { input: [[n; 2]; 2] },
            // 30
            GateKind::InitsOrTeardownsInitialPair {
                timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                setup: [n; 2],
                set_idxes: [0; 2],
            },
        ]
    }

    #[test]
    fn all_gatekind_variants_round_trip() {
        let samples: Vec<GateKind> = gatekind_samples();
        assert_eq!(samples.len(), 30);
        let json = serde_json::to_string(&samples).unwrap();
        let back: Vec<GateKind> = serde_json::from_str(&json).unwrap();
        assert_eq!(back.len(), samples.len());
        assert_eq!(back, samples);
    }

    fn sample_layer() -> GKRLayerDescription {
        use NoFieldStructuredExpression as E;
        // out = (w0 * w1) + 2*w2 + 3, also enforced as a max-quadratic constraint.
        let mq = super::super::NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![(blw(0), vec![(1u32, blw(1))].into_boxed_slice())]
                .into_boxed_slice(),
            linear_terms: vec![(2u32, blw(2))].into_boxed_slice(),
            constant: 3,
        };
        let expr = E::Sum(vec![
            E::Product(vec![E::Place(blw(0)), E::Place(blw(1))]),
            E::Product(vec![E::Place(blw(0)), E::Place(blw(1))]), // duplicate -> must CSE
            E::Place(blw(2)),
            E::Constant(3),
        ]);
        GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            gates: vec![
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::CopyInBaseField {
                        input: blw(0),
                        output: inner(1, 0),
                    },
                },
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::MaxQuadratic {
                        input: mq,
                        expression: expr,
                        output: inner(1, 1),
                    },
                },
            ],
            intermediate_layer_width: Some(2),
        }
    }

    #[test]
    fn lowers_copy_and_max_quadratic() {
        let layer = sample_layer();
        let scratch = BTreeMap::new();
        let cg = lower_layer(&layer, &scratch);
        assert_eq!(cg.gates.len(), 2);
        assert!(cg.gates_external.is_empty());
        // CSE: the duplicate Product subexpression interned once.
        let product_count = cg
            .arena
            .nodes
            .iter()
            .filter(|n| matches!(n, ExprNode::Product { .. }))
            .count();
        assert_eq!(product_count, 1, "duplicate product must be CSE-merged");
        cg.verify().expect("verify");
    }

    #[test]
    fn scratch_backed_max_quadratic_is_prefill() {
        let layer = sample_layer();
        let mut scratch = BTreeMap::new();
        scratch.insert(inner(1, 1), 0usize); // MaxQuadratic output is scratch-backed
        let cg = lower_layer(&layer, &scratch);
        let mq_gate = cg
            .gates
            .iter()
            .find(|g| matches!(g.kind, GateKind::MaxQuadratic { .. }))
            .unwrap();
        assert!(matches!(
            mq_gate.dst[0].forward_source,
            ForwardSource::ScratchPrefill
        ));
        // The Copy output, also writing an inner-layer addr, stays Computed even if
        // it were scratch-mapped — only MaxQuadratic flips.
        let copy_gate = cg
            .gates
            .iter()
            .find(|g| matches!(g.kind, GateKind::CopyInBaseField { .. }))
            .unwrap();
        assert!(matches!(copy_gate.dst[0].forward_source, ForwardSource::Computed));
        cg.verify().expect("verify");
    }

    #[test]
    fn serde_round_trip() {
        let cg = lower_layer(&sample_layer(), &BTreeMap::new());
        let json = serde_json::to_string(&cg).expect("serialize");
        let back: CodegenLayer = serde_json::from_str(&json).expect("deserialize");
        back.verify().expect("verify after round-trip");
        assert_eq!(back.arena.nodes.len(), cg.arena.nodes.len());
    }

    #[test]
    fn cross_gate_place_sharing() {
        // blw(0) is read by BOTH the Copy gate and the MaxQuadratic gate. The shared
        // per-layer arena must intern it ONCE — the spec's "cross-gate is the largest
        // win" (finding 8: previously unproven by the suite).
        let cg = lower_layer(&sample_layer(), &BTreeMap::new());
        let blw0_places = cg
            .arena
            .nodes
            .iter()
            .filter(|n| matches!(n, ExprNode::Place { addr, .. } if *addr == blw(0)))
            .count();
        assert_eq!(blw0_places, 1, "blw(0) read by two gates must be a single Place node");
    }

    #[test]
    fn resolve_links_intra_layer_producer_not_a_fresh_place() {
        // Direct ArenaBuilder check of the producer->consumer edge mechanism
        // (finding 6): a same-layer produced address resolves to its GateOutput, not a
        // fresh Place; an external address resolves to a Place.
        let mut b = ArenaBuilder::default();
        let cache_addr = GKRAddress::Cached { layer: 0, offset: 0 };
        let produced = b.add_gate_output(ProducerId::Cache(0), 0, Domain::Ext, cache_addr);
        // a consumer reading the cache address must get the SAME node (the producer).
        let consumed = b.resolve(cache_addr, Domain::Ext);
        assert_eq!(consumed, produced, "intra-layer address must resolve to its producer");
        assert!(matches!(b.nodes[consumed.0 as usize], ExprNode::GateOutput { .. }));
        // an external address has no producer -> a Place leaf, a distinct node.
        let external = b.resolve(blw(9), Domain::Base);
        assert_ne!(external, produced);
        assert!(matches!(b.nodes[external.0 as usize], ExprNode::Place { .. }));
    }

    // -----------------------------------------------------------------------
    // Task 2: metadata_fixtures + metadata tests
    // -----------------------------------------------------------------------

    /// Build one `NoFieldGKRRelation` per variant (all 30), grouped by
    /// (outputs, num_challenges, out_domain) class, panicking variants included.
    /// Cross-checked against `relation_metadata` and `num_challenges()`.
    fn metadata_fixtures() -> Vec<(NoFieldGKRRelation, RelationMeta)> {
        use super::super::{
            CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
            InitsOrTeardownsTimestampAndValue, NoFieldGKRRelation as R,
            NoFieldMaxQuadraticConstraintsGKRRelation, NoFieldMaxQuadraticGKRRelation,
            NoFieldSpecialMemoryContributionRelation, NoFieldStructuredExpression as E,
        };
        use crate::definitions::gkr::{
            NoFieldLinearRelation, NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
            RamWordRepresentation,
        };

        let a0 = blw(0);
        let a1 = blw(1);
        let out0 = inner(1, 0);
        let out1 = inner(1, 1);

        let lin = NoFieldLinearRelation {
            linear_terms: vec![(1u32, a0)].into_boxed_slice(),
            constant: 0,
        };
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![(1u32, a0)].into_boxed_slice(),
            constant: 0,
        };
        let mem_desc = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::Constant(0),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let scl = NoFieldSingleColumnLookupRelation {
            input: lin.clone(),
            lookup_set_index: 0,
        };
        let vl = NoFieldVectorLookupRelation {
            columns: vec![lin.clone()].into_boxed_slice(),
            lookup_set_index: 0,
        };

        let m_base_1_1 = RelationMeta { outputs: 1, num_challenges: 1, out_domain: Domain::Base };
        let m_base_0_1 = RelationMeta { outputs: 0, num_challenges: 1, out_domain: Domain::Base };
        let m_ext_1_1  = RelationMeta { outputs: 1, num_challenges: 1, out_domain: Domain::Ext };
        let m_ext_2_2  = RelationMeta { outputs: 2, num_challenges: 2, out_domain: Domain::Ext };

        vec![
            // --- class (1, 1, Base) ---
            (R::LinearBaseFieldRelation { input: lin.clone(), output: out0 }, m_base_1_1),
            (R::MaxQuadratic { input: mq.clone(), expression: E::Constant(0), output: out0 }, m_base_1_1),
            (R::CopyInBaseField { input: a0, output: out0 }, m_base_1_1),
            (R::MaterializeSingleLookupInput { input: scl.clone(), output: out0, range_check_width: 16 }, m_base_1_1),
            // --- class (0, 1, Base) ---
            (R::EnforceSingleMaxQuadraticConstraint {
                input: mq.clone(),
                expression: E::Constant(0),
            }, m_base_0_1),
            (R::EnforceConstraintsMaxQuadratic {
                input: NoFieldMaxQuadraticConstraintsGKRRelation {
                    quadratic_terms: vec![].into_boxed_slice(),
                    linear_terms: vec![].into_boxed_slice(),
                    constants: vec![].into_boxed_slice(),
                },
            }, m_base_0_1),
            // --- class (1, 1, Ext) ---
            (R::CopyInExtensionField { input: a0, output: out0 }, m_ext_1_1),
            (R::InitialGrandProductFromCaches { input: [a0, a1], output: out0 }, m_ext_1_1),
            (R::InitialGrandProductWithoutCaches {
                input: [mem_desc.clone(), mem_desc.clone()],
                output: out0,
            }, m_ext_1_1),
            (R::UnbalancedGrandProductWithCache { scalar: a0, input: a1, output: out0 }, m_ext_1_1),
            // MaterializeGrandProductTermExpression: panicking variant — still covered by metadata
            (R::MaterializeGrandProductTermExpression { input: mem_desc.clone(), output: out0 }, m_ext_1_1),
            (R::TrivialProduct { input: [a0, a1], output: out0 }, m_ext_1_1),
            (R::MaskIntoIdentityProduct { input: a0, mask: a1, output: out0 }, m_ext_1_1),
            (R::MaterializedVectorLookupInput { input: vl.clone(), output: out0 }, m_ext_1_1),
            (R::InitsOrTeardownsInitialPair {
                timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                setup: [a0, a1],
                output: out0,
                set_idxes: [0, 1],
            }, m_ext_1_1),
            // --- class (2, 2, Ext) ---
            (R::LookupWithCachedDensAndSetup { input: [a0, a1], setup: [a0, a1], output: [out0, out1] }, m_ext_2_2),
            (R::LookupWithDensAndSetupExpressions {
                input: (a0, vl.clone()),
                setup: (a0, vec![a1].into_boxed_slice()),
                output: [out0, out1],
            }, m_ext_2_2),
            (R::LookupWithDensAndCachedSetup {
                input: (a0, vl.clone()),
                setup: (a0, a1),
                output: [out0, out1],
            }, m_ext_2_2),
            (R::LookupPairFromBaseInputs { input: [scl.clone(), scl.clone()], output: [out0, out1], range_check_width: 16 }, m_ext_2_2),
            (R::LookupPairFromMaterializedBaseInputs { input: [a0, a1], output: [out0, out1] }, m_ext_2_2),
            (R::LookupFromMaterializedBaseInputWithSetup { input: a0, setup: [a0, a1], output: [out0, out1] }, m_ext_2_2),
            (R::LookupUnbalancedPairWithMaterializedBaseInputs { input: [a0, a1], remainder: a0, output: [out0, out1] }, m_ext_2_2),
            (R::LookupPairFromVectorInputs { input: [vl.clone(), vl.clone()], output: [out0, out1] }, m_ext_2_2),
            (R::LookupPairFromMaterializedVectorInputs { input: [a0, a1], output: [out0, out1] }, m_ext_2_2),
            // LookupFromVectorInputWithSetup: panicking variant — still covered by metadata
            (R::LookupFromVectorInputWithSetup {
                input: vl.clone(),
                setup: (a0, vec![a1].into_boxed_slice()),
                output: [out0, out1],
            }, m_ext_2_2),
            (R::LookupFromMaterializedVectorInputWithSetup { input: a0, setup: [a0, a1], output: [out0, out1] }, m_ext_2_2),
            (R::LookupPairFromCachedVectorInputs { input: [a0, a1], output: [out0, out1] }, m_ext_2_2),
            // LookupUnbalancedPairWithVectorInputs: panicking variant — still covered by metadata
            (R::LookupUnbalancedPairWithVectorInputs { input: [a0, a1], remainder: vl.clone(), output: [out0, out1] }, m_ext_2_2),
            // LookupUnbalancedPairWithMaterializedVectorInputs: panicking variant — still covered by metadata
            (R::LookupUnbalancedPairWithMaterializedVectorInputs { input: [a0, a1], remainder: a0, output: [out0, out1] }, m_ext_2_2),
            (R::AggregateLookupRationalPair { input: [[a0, a1], [a0, a1]], output: [out0, out1] }, m_ext_2_2),
        ]
    }

    #[test]
    fn metadata_table_is_total_and_consistent() {
        for (rel, meta) in metadata_fixtures() {
            let m = relation_metadata(&rel);
            assert_eq!(m.outputs, meta.outputs, "{:?}", rel);
            assert_eq!(m.num_challenges, meta.num_challenges, "{:?}", rel);
            assert_eq!(m.out_domain, meta.out_domain, "{:?}", rel);
        }
    }

    /// Returns true for variants whose `num_challenges()` is implemented (does NOT panic).
    /// Panicking variants (mod.rs:1688 catch-all `a @ _`):
    ///   - MaterializeGrandProductTermExpression (line 1688 catch-all)
    ///   - LookupFromVectorInputWithSetup         (line 1688 catch-all)
    ///   - LookupUnbalancedPairWithVectorInputs   (line 1688 catch-all)
    ///   - LookupUnbalancedPairWithMaterializedVectorInputs (line 1688 catch-all)
    ///   - InitsOrTeardownsInitialPair            (line 1688 catch-all)
    ///
    /// When a panicking arm is implemented in `mod.rs`, remove that variant from
    /// this list; the prover-side cross-val (Task 13) then covers it in the full check.
    fn cs_num_challenges_covered(rel: &NoFieldGKRRelation) -> bool {
        use NoFieldGKRRelation as R;
        !matches!(
            rel,
            R::MaterializeGrandProductTermExpression { .. }
                | R::LookupFromVectorInputWithSetup { .. }
                | R::LookupUnbalancedPairWithVectorInputs { .. }
                | R::LookupUnbalancedPairWithMaterializedVectorInputs { .. }
                | R::InitsOrTeardownsInitialPair { .. }
        )
    }

    #[test]
    fn metadata_num_challenges_matches_cs_oracle() {
        for (rel, _) in metadata_fixtures() {
            if cs_num_challenges_covered(&rel) {
                assert_eq!(
                    relation_metadata(&rel).num_challenges as usize,
                    rel.num_challenges(),
                    "metadata disagrees with cs::num_challenges() for {:?}",
                    rel
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Task 4: grand-product / product family lowering tests
    // -----------------------------------------------------------------------

    /// Build a `GKRLayerDescription` with a single gate (no external connections).
    fn single_gate_layer(rel: NoFieldGKRRelation) -> GKRLayerDescription {
        GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: rel,
            }],
            intermediate_layer_width: Some(1),
        }
    }

    #[test]
    fn lowers_trivial_product_two_inputs() {
        let layer = single_gate_layer(NoFieldGKRRelation::TrivialProduct {
            input: [
                GKRAddress::InnerLayer { layer: 0, offset: 0 },
                GKRAddress::InnerLayer { layer: 0, offset: 1 },
            ],
            output: GKRAddress::InnerLayer { layer: 1, offset: 0 },
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(matches!(g.kind, GateKind::TrivialProduct { .. }));
        assert_eq!(g.dst.len(), 1);
        cg.verify().unwrap();
    }

    #[test]
    fn lowers_initial_grand_product_from_caches() {
        let layer = single_gate_layer(NoFieldGKRRelation::InitialGrandProductFromCaches {
            input: [blw(0), blw(1)],
            output: inner(1, 0),
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(matches!(g.kind, GateKind::InitialGrandProductFromCaches { .. }));
        assert_eq!(g.dst.len(), 1);
        cg.verify().unwrap();
    }

    #[test]
    fn lowers_unbalanced_grand_product_with_cache() {
        let layer = single_gate_layer(NoFieldGKRRelation::UnbalancedGrandProductWithCache {
            scalar: blw(0),
            input: blw(1),
            output: inner(1, 0),
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(matches!(g.kind, GateKind::UnbalancedGrandProductWithCache { .. }));
        assert_eq!(g.dst.len(), 1);
        cg.verify().unwrap();
    }

    #[test]
    fn lowers_mask_into_identity_product_mixed_domains() {
        use super::super::{
            CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
            NoFieldSpecialMemoryContributionRelation,
        };
        use crate::definitions::gkr::RamWordRepresentation;

        // mask=Base, input=Ext — verify both Place nodes have the right domain.
        let layer = single_gate_layer(NoFieldGKRRelation::MaskIntoIdentityProduct {
            input: blw(0),
            mask: blw(1),
            output: inner(1, 0),
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(matches!(g.kind, GateKind::MaskIntoIdentityProduct { .. }));
        assert_eq!(g.dst.len(), 1);
        // blw(0) is the input -> Ext; blw(1) is the mask -> Base.
        let has_ext_place = cg.arena.nodes.iter().any(|n| {
            matches!(n, ExprNode::Place { addr, domain: Domain::Ext, .. } if *addr == blw(0))
        });
        let has_base_place = cg.arena.nodes.iter().any(|n| {
            matches!(n, ExprNode::Place { addr, domain: Domain::Base, .. } if *addr == blw(1))
        });
        assert!(has_ext_place, "input (blw(0)) must be Ext-domain Place");
        assert!(has_base_place, "mask (blw(1)) must be Base-domain Place");
        cg.verify().unwrap();
    }

    // -----------------------------------------------------------------------
    // Task 5: lookup materialization lowering tests
    // -----------------------------------------------------------------------

    #[test]
    fn lowers_materialize_single_lookup_input() {
        use super::super::{NoFieldGKRRelation as R};
        use crate::definitions::gkr::{NoFieldLinearRelation, NoFieldSingleColumnLookupRelation};

        // Build a 2-term linear relation: 1*blw(0) + 2*blw(1) + 0
        let lin = NoFieldLinearRelation {
            linear_terms: vec![(1u32, blw(0)), (2u32, blw(1))].into_boxed_slice(),
            constant: 0,
        };
        let scl = NoFieldSingleColumnLookupRelation { input: lin, lookup_set_index: 7 };
        let output = inner(1, 0);
        let layer = single_gate_layer(R::MaterializeSingleLookupInput {
            input: scl,
            output,
            range_check_width: 16,
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(
            matches!(g.kind, GateKind::MaterializeSingleLookupInput { range_check_width: 16, .. }),
            "expected MaterializeSingleLookupInput with range_check_width=16, got {:?}",
            g.kind
        );
        assert_eq!(g.dst.len(), 1);
        // lookup_set_index must be preserved
        if let GateKind::MaterializeSingleLookupInput { input: ref scl_ir, .. } = g.kind {
            assert_eq!(scl_ir.lookup_set_index, 7);
            assert_eq!(scl_ir.column.terms.len(), 2);
        }
        // Fix 1: output node must be Base-domain (materialized single lookup -> base-field result).
        assert_eq!(
            cg.arena.nodes[g.dst[0].node.0 as usize].domain(),
            Domain::Base,
            "single-lookup output node must be Base"
        );
        cg.verify().unwrap();
    }

    #[test]
    fn lowers_materialized_vector_lookup_input() {
        use super::super::{NoFieldGKRRelation as R};
        use crate::definitions::gkr::{NoFieldLinearRelation, NoFieldVectorLookupRelation};

        // Build a one-column vector lookup: 1*blw(0) + 0
        let lin = NoFieldLinearRelation {
            linear_terms: vec![(1u32, blw(0))].into_boxed_slice(),
            constant: 0,
        };
        let vl = NoFieldVectorLookupRelation {
            columns: vec![lin].into_boxed_slice(),
            lookup_set_index: 3,
        };
        let output = inner(1, 0);
        let layer = single_gate_layer(R::MaterializedVectorLookupInput {
            input: vl,
            output,
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(
            matches!(g.kind, GateKind::MaterializedVectorLookupInput { .. }),
            "expected MaterializedVectorLookupInput, got {:?}",
            g.kind
        );
        assert_eq!(g.dst.len(), 1);
        // Fix 2: output node must be Ext-domain (materialized vector lookup -> extension-field result).
        assert_eq!(
            cg.arena.nodes[g.dst[0].node.0 as usize].domain(),
            Domain::Ext,
            "vector-lookup output node must be Ext"
        );
        cg.verify().unwrap();
    }

    // -----------------------------------------------------------------------
    // Task 3: domain-threading guard tests
    // -----------------------------------------------------------------------

    /// A layer with a single CopyInExtensionField gate.
    fn ext_copy_layer() -> GKRLayerDescription {
        GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::CopyInExtensionField {
                    input: inner(0, 5),
                    output: inner(1, 0),
                },
            }],
            intermediate_layer_width: Some(1),
        }
    }

    /// The input Place node for a CopyInExtensionField gate must carry Domain::Ext.
    #[test]
    fn ext_copy_places_are_ext_domain() {
        let layer = ext_copy_layer();
        let cg = lower_layer(&layer, &BTreeMap::new());
        // The input address (inner(0,5)) has no intra-layer producer, so it becomes a
        // Place leaf.  That leaf must be Domain::Ext because the copy is extension-field.
        let has_ext_place = cg.arena.nodes.iter().any(|n| {
            matches!(n, ExprNode::Place { domain: Domain::Ext, .. })
        });
        assert!(has_ext_place, "ext copy input must be an Ext-domain Place");
        // Symmetry: no Base Place should exist in a pure ext-copy layer.
        let has_base_place = cg.arena.nodes.iter().any(|n| {
            matches!(n, ExprNode::Place { domain: Domain::Base, .. })
        });
        assert!(!has_base_place, "ext copy layer must not produce Base-domain Place nodes");
        cg.verify().expect("verify");
    }

    /// All Place nodes produced for a pure max-quadratic layer must be Domain::Base.
    #[test]
    fn max_quad_operand_places_are_base_domain() {
        // sample_layer() contains a MaxQuadratic gate (plus a CopyInBaseField gate);
        // every operand address is a base-layer witness, so all Place nodes must be Base.
        let cg = lower_layer(&sample_layer(), &BTreeMap::new());
        let has_ext_place = cg.arena.nodes.iter().any(|n| {
            matches!(n, ExprNode::Place { domain: Domain::Ext, .. })
        });
        assert!(!has_ext_place, "max-quad operands must all be Base-domain Place nodes");
        cg.verify().expect("verify");
    }

    // -----------------------------------------------------------------------
    // Task 6: two-output lookup family tests
    // -----------------------------------------------------------------------

    #[test]
    fn lowers_lookup_pair_from_materialized_base_inputs() {
        let layer = single_gate_layer(NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
            input: [inner(0, 0), inner(0, 1)],
            output: [inner(1, 0), inner(1, 1)],
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        let GateKind::LookupPairFromMaterializedBaseInputs { input } = &g.kind else {
            panic!("wrong gate kind");
        };
        assert_eq!(cg.arena.nodes[input[0].0 as usize].domain(), Domain::Base, "input[0] must be Base");
        assert_eq!(cg.arena.nodes[input[1].0 as usize].domain(), Domain::Base, "input[1] must be Base");
        assert_eq!(g.dst.len(), 2);
        assert_ne!(
            g.dst[0].node.0, g.dst[1].node.0,
            "the two outputs must be distinct GateOutput nodes"
        );
        cg.verify().unwrap();
    }

    #[test]
    fn lowers_lookup_with_cached_dens_and_setup_mixed_domains() {
        // Verified against the prover kernel: input[0]/setup[0] are Base,
        // input[1]/setup[1] are Ext (nums in inputs_in_base, dens in inputs_in_extension).
        let layer = single_gate_layer(NoFieldGKRRelation::LookupWithCachedDensAndSetup {
            input: [blw(0), blw(1)],
            setup: [blw(2), blw(3)],
            output: [inner(1, 0), inner(1, 1)],
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        let GateKind::LookupWithCachedDensAndSetup { input, setup } = &g.kind else {
            panic!("wrong gate kind");
        };
        assert_eq!(cg.arena.nodes[input[0].0 as usize].domain(), Domain::Base, "input[0] must be Base");
        assert_eq!(cg.arena.nodes[input[1].0 as usize].domain(), Domain::Ext, "input[1] must be Ext");
        assert_eq!(cg.arena.nodes[setup[0].0 as usize].domain(), Domain::Base, "setup[0] must be Base");
        assert_eq!(cg.arena.nodes[setup[1].0 as usize].domain(), Domain::Ext, "setup[1] must be Ext");
        assert_eq!(g.dst.len(), 2);
        cg.verify().unwrap();
    }
}
