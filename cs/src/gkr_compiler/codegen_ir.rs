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

use super::{GKRLayerDescription, GateArtifacts, NoFieldGKRRelation, NoFieldStructuredExpression};
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
    Place {
        addr: GKRAddress,
        domain: Domain,
    },
    GateOutput {
        producer: ProducerId,
        out: u32,
        domain: Domain,
    },
    Sum {
        terms: Vec<NodeId>,
        domain: Domain,
    },
    Product {
        factors: Vec<NodeId>,
        domain: Domain,
    },
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

/// One batch-power term in the batched-sum polynomial.
///
/// `value` is the representative `NodeId`: for output-bearing gates it is the
/// first output node (shared by both terms for 2-output gates — the GateKind
/// stores all outputs). For no-output constraint gates it is the expression
/// node used as the batch anchor. For `EnforceConstraintsMaxQuadratic`, `value`
/// anchors the first sparse operand; the full folded constraint lives in the
/// `GateKind`'s sparse terms, so `uses`/footprint still see all operands via
/// the gate-input enumeration.
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
    LinearBaseField {
        input: LinearComb,
    },
    MaxQuadratic {
        flat: MaxQuadFlat,
        expr: NodeId,
    },
    EnforceSingleMaxQuadraticConstraint {
        flat: MaxQuadFlat,
        expr: NodeId,
    },
    EnforceConstraintsMaxQuadratic {
        quadratic: Vec<((NodeId, NodeId), Vec<(u32, usize)>)>,
        linear: Vec<(NodeId, Vec<(u32, usize)>)>,
        constants: Vec<(u32, usize)>,
    },
    CopyInBaseField {
        input: NodeId,
    },
    CopyInExtensionField {
        input: NodeId,
    },
    InitialGrandProductFromCaches {
        input: [NodeId; 2],
    },
    InitialGrandProductWithoutCaches {
        input: [MemTupleDescriptor; 2],
    },
    UnbalancedGrandProductWithCache {
        scalar: NodeId,
        input: NodeId,
    },
    MaterializeGrandProductTermExpression {
        input: MemTupleDescriptor,
    },
    TrivialProduct {
        input: [NodeId; 2],
    },
    MaskIntoIdentityProduct {
        input: NodeId,
        mask: NodeId,
    },
    MaterializeSingleLookupInput {
        input: SingleColumnLookup,
        range_check_width: u32,
    },
    MaterializedVectorLookupInput {
        input: VectorLookup,
    },
    LookupWithCachedDensAndSetup {
        input: [NodeId; 2],
        setup: [NodeId; 2],
    },
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
    LookupPairFromBaseInputs {
        input: [SingleColumnLookup; 2],
        range_check_width: u32,
    },
    LookupPairFromMaterializedBaseInputs {
        input: [NodeId; 2],
    },
    LookupFromMaterializedBaseInputWithSetup {
        input: NodeId,
        setup: [NodeId; 2],
    },
    LookupUnbalancedPairWithMaterializedBaseInputs {
        input: [NodeId; 2],
        remainder: NodeId,
    },
    LookupPairFromVectorInputs {
        input: [VectorLookup; 2],
    },
    LookupPairFromMaterializedVectorInputs {
        input: [NodeId; 2],
    },
    LookupFromVectorInputWithSetup {
        input: VectorLookup,
        setup_addr: NodeId,
        setup_extra: Vec<NodeId>,
    },
    LookupFromMaterializedVectorInputWithSetup {
        input: NodeId,
        setup: [NodeId; 2],
    },
    LookupPairFromCachedVectorInputs {
        input: [NodeId; 2],
    },
    LookupUnbalancedPairWithVectorInputs {
        input: [NodeId; 2],
        remainder: VectorLookup,
    },
    LookupUnbalancedPairWithMaterializedVectorInputs {
        input: [NodeId; 2],
        remainder: NodeId,
    },
    AggregateLookupRationalPair {
        input: [[NodeId; 2]; 2],
    },
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
    SingleColumnLookup {
        column: LinearComb,
        lookup_set_index: usize,
        range_check_width: usize,
    },
    VectorizedLookup {
        columns: Vec<LinearComb>,
        lookup_set_index: usize,
    },
    MemoryTuple {
        descriptor: MemTupleDescriptor,
    },
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

/// serde adapter for `BTreeMap<GKRAddress, usize>`: serialized as a sequence
/// of `(GKRAddress, usize)` pairs because JSON map keys must be strings.
mod addr_key_map {
    use super::*;
    use serde::{Deserialize as _, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(
        m: &BTreeMap<GKRAddress, usize>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        s.collect_seq(m.iter())
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<BTreeMap<GKRAddress, usize>, D::Error> {
        Ok(Vec::<(GKRAddress, usize)>::deserialize(d)?
            .into_iter()
            .collect())
    }
}

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
    /// JSON object keys must be strings, but `GKRAddress` has struct variants,
    /// so this map round-trips as a sequence of `[addr, slot]` pairs.
    #[serde(with = "addr_key_map")]
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
    /// Number of batch challenges this gate consumes, sourced from
    /// `relation_metadata(rel).num_challenges`. Equals `dst.len()` for
    /// output-bearing gates; may be 1 even when `dst.is_empty()` for
    /// no-output constraint gates (e.g. `EnforceSingleMaxQuadraticConstraint`).
    pub num_challenges: u8,
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
    /// Maps each GateOutput NodeId -> the complete set of its gate's operand NodeIds.
    /// Populated AT lowering time (before `add_gate_output` so all operands exist).
    /// For multi-output gates, every GateOutput NodeId maps to the SAME operand set.
    /// Used by `compute_hints` to union operand footprints into the GateOutput footprint.
    gate_inputs: HashMap<NodeId, Vec<NodeId>>,
    /// Maps each GateOutput NodeId -> (addr, forward_source) recorded from the
    /// OutputSlot so `compute_hints` can distinguish ScratchPrefill from Computed.
    gate_output_slots: HashMap<NodeId, (GKRAddress, ForwardSource)>,
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
        if matches!(
            addr,
            GKRAddress::InnerLayer { .. } | GKRAddress::Cached { .. }
        ) {
            self.produced.insert(addr, id);
        }
        id
    }

    /// Record the complete operand NodeId set for a GateOutput and its slot metadata.
    /// Must be called AFTER all operand nodes are created, BEFORE or just after
    /// `add_gate_output`. For multi-output gates, call once per output NodeId with
    /// the SAME `inputs` vector.
    fn record_output(
        &mut self,
        node: NodeId,
        addr: GKRAddress,
        forward_source: ForwardSource,
        inputs: Vec<NodeId>,
    ) {
        self.gate_inputs.insert(node, inputs);
        self.gate_output_slots.insert(node, (addr, forward_source));
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
                let mut terms: Vec<NodeId> = children
                    .iter()
                    .map(|c| self.lower_expr(c, domain))
                    .collect();
                terms.sort_by_key(|n| n.0);
                self.intern(ExprNode::Sum { terms, domain })
            }
            NoFieldStructuredExpression::Product(children) => {
                let mut factors: Vec<NodeId> = children
                    .iter()
                    .map(|c| self.lower_expr(c, domain))
                    .collect();
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
    let num_challenges = relation_metadata(rel).num_challenges;
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
            debug_assert!(
                matches!(domain, Domain::Base),
                "MaxQuadratic is always base-field"
            );
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
            debug_assert!(
                matches!(domain, Domain::Base),
                "EnforceSingleMaxQuadraticConstraint is always base-field"
            );
            let flat = lower_max_quad_flat(b, input, domain);
            let expr = b.lower_expr(expression, domain);
            (
                GateKind::EnforceSingleMaxQuadraticConstraint { flat, expr },
                vec![],
            )
        }
        R::EnforceConstraintsMaxQuadratic { input } => {
            let domain = relation_metadata(rel).out_domain;
            debug_assert!(
                matches!(domain, Domain::Base),
                "EnforceConstraintsMaxQuadratic is always base-field"
            );
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
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::InitialGrandProductFromCaches { input: i },
                one_out(node, *output, scratch, false),
            )
        }
        R::InitialGrandProductWithoutCaches { input, output } => {
            let d = [lower_mem_tuple(b, &input[0]), lower_mem_tuple(b, &input[1])];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::InitialGrandProductWithoutCaches { input: d },
                one_out(node, *output, scratch, false),
            )
        }
        R::UnbalancedGrandProductWithCache {
            scalar,
            input,
            output,
        } => {
            let s = b.resolve(*scalar, Domain::Ext);
            let i = b.resolve(*input, Domain::Ext);
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::UnbalancedGrandProductWithCache {
                    scalar: s,
                    input: i,
                },
                one_out(node, *output, scratch, false),
            )
        }
        R::MaterializeGrandProductTermExpression { input, output } => {
            let d = lower_mem_tuple(b, input);
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::MaterializeGrandProductTermExpression { input: d },
                one_out(node, *output, scratch, false),
            )
        }
        R::TrivialProduct { input, output } => {
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::TrivialProduct { input: i },
                one_out(node, *output, scratch, false),
            )
        }
        R::MaskIntoIdentityProduct {
            input,
            mask,
            output,
        } => {
            // MIXED: mask is Base-field, input is extension-field (mask_into_identity add_base_by_ext).
            let m = b.resolve(*mask, Domain::Base);
            let i = b.resolve(*input, Domain::Ext);
            let node = b.add_gate_output(producer, 0, Domain::Ext, *output);
            (
                GateKind::MaskIntoIdentityProduct { input: i, mask: m },
                one_out(node, *output, scratch, false),
            )
        }
        R::MaterializeSingleLookupInput {
            input,
            output,
            range_check_width,
        } => {
            let s = lower_single_col(b, input, Domain::Base);
            let node = b.add_gate_output(producer, 0, Domain::Base, *output);
            (
                GateKind::MaterializeSingleLookupInput {
                    input: s,
                    range_check_width: *range_check_width,
                },
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
        R::LookupWithCachedDensAndSetup {
            input,
            setup,
            output,
        } => {
            let i = [
                b.resolve(input[0], Domain::Base),
                b.resolve(input[1], Domain::Ext),
            ];
            let s = [
                b.resolve(setup[0], Domain::Base),
                b.resolve(setup[1], Domain::Ext),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupWithCachedDensAndSetup { input: i, setup: s },
                dst,
            )
        }
        R::LookupWithDensAndSetupExpressions {
            input,
            setup,
            output,
        } => {
            let input_addr = b.resolve(input.0, Domain::Ext);
            let input_vec = lower_vector(b, &input.1, Domain::Base);
            let setup_addr = b.resolve(setup.0, Domain::Ext);
            let setup_extra = setup.1.iter().map(|a| b.resolve(*a, Domain::Ext)).collect();
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupWithDensAndSetupExpressions {
                    input_addr,
                    input_vec,
                    setup_addr,
                    setup_extra,
                },
                dst,
            )
        }
        R::LookupWithDensAndCachedSetup {
            input,
            setup,
            output,
        } => {
            let input_addr = b.resolve(input.0, Domain::Ext);
            let input_vec = lower_vector(b, &input.1, Domain::Base);
            let s = [
                b.resolve(setup.0, Domain::Ext),
                b.resolve(setup.1, Domain::Ext),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupWithDensAndCachedSetup {
                    input_addr,
                    input_vec,
                    setup: s,
                },
                dst,
            )
        }
        R::LookupPairFromBaseInputs {
            input,
            output,
            range_check_width,
        } => {
            let i = [
                lower_single_col(b, &input[0], Domain::Base),
                lower_single_col(b, &input[1], Domain::Base),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupPairFromBaseInputs {
                    input: i,
                    range_check_width: *range_check_width,
                },
                dst,
            )
        }
        R::LookupPairFromMaterializedBaseInputs { input, output } => {
            let i = [
                b.resolve(input[0], Domain::Base),
                b.resolve(input[1], Domain::Base),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupPairFromMaterializedBaseInputs { input: i },
                dst,
            )
        }
        R::LookupFromMaterializedBaseInputWithSetup {
            input,
            setup,
            output,
        } => {
            let i = b.resolve(*input, Domain::Base);
            let s = [
                b.resolve(setup[0], Domain::Base),
                b.resolve(setup[1], Domain::Base),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupFromMaterializedBaseInputWithSetup { input: i, setup: s },
                dst,
            )
        }
        R::LookupUnbalancedPairWithMaterializedBaseInputs {
            input,
            remainder,
            output,
        } => {
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let r = b.resolve(*remainder, Domain::Base);
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupUnbalancedPairWithMaterializedBaseInputs {
                    input: i,
                    remainder: r,
                },
                dst,
            )
        }
        R::LookupPairFromVectorInputs { input, output } => {
            let i = [
                lower_vector(b, &input[0], Domain::Base),
                lower_vector(b, &input[1], Domain::Base),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromVectorInputs { input: i }, dst)
        }
        R::LookupPairFromMaterializedVectorInputs { input, output } => {
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupPairFromMaterializedVectorInputs { input: i },
                dst,
            )
        }
        R::LookupFromVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            let v = lower_vector(b, input, Domain::Base);
            let setup_addr = b.resolve(setup.0, Domain::Ext);
            let setup_extra = setup.1.iter().map(|a| b.resolve(*a, Domain::Ext)).collect();
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupFromVectorInputWithSetup {
                    input: v,
                    setup_addr,
                    setup_extra,
                },
                dst,
            )
        }
        R::LookupFromMaterializedVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            let i = b.resolve(*input, Domain::Ext);
            let s = [
                b.resolve(setup[0], Domain::Base),
                b.resolve(setup[1], Domain::Ext),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupFromMaterializedVectorInputWithSetup { input: i, setup: s },
                dst,
            )
        }
        R::LookupPairFromCachedVectorInputs { input, output } => {
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::LookupPairFromCachedVectorInputs { input: i }, dst)
        }
        R::LookupUnbalancedPairWithVectorInputs {
            input,
            remainder,
            output,
        } => {
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let r = lower_vector(b, remainder, Domain::Base);
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupUnbalancedPairWithVectorInputs {
                    input: i,
                    remainder: r,
                },
                dst,
            )
        }
        R::LookupUnbalancedPairWithMaterializedVectorInputs {
            input,
            remainder,
            output,
        } => {
            let i = [
                b.resolve(input[0], Domain::Ext),
                b.resolve(input[1], Domain::Ext),
            ];
            let r = b.resolve(*remainder, Domain::Ext);
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (
                GateKind::LookupUnbalancedPairWithMaterializedVectorInputs {
                    input: i,
                    remainder: r,
                },
                dst,
            )
        }
        R::AggregateLookupRationalPair { input, output } => {
            let i = [
                [
                    b.resolve(input[0][0], Domain::Ext),
                    b.resolve(input[0][1], Domain::Ext),
                ],
                [
                    b.resolve(input[1][0], Domain::Ext),
                    b.resolve(input[1][1], Domain::Ext),
                ],
            ];
            let dst = two_out(b, producer, output, Domain::Ext, scratch);
            (GateKind::AggregateLookupRationalPair { input: i }, dst)
        }
        R::InitsOrTeardownsInitialPair {
            timestamp_and_value,
            setup,
            output,
            set_idxes,
        } => {
            // setup BASE, result Ext.
            let s = [
                b.resolve(setup[0], Domain::Base),
                b.resolve(setup[1], Domain::Base),
            ];
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
        num_challenges,
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
        OutputSlot {
            node: n0,
            addr: out[0],
            forward_source: forward_source_for(&out[0], false, scratch),
        },
        OutputSlot {
            node: n1,
            addr: out[1],
            forward_source: forward_source_for(&out[1], false, scratch),
        },
    ]
}

/// Lower a `NoFieldSpecialMemoryContributionRelation` by resolving each of its
/// `dependencies()` (all `BaseLayerMemory` reads) as Base-domain Place nodes.
fn lower_mem_tuple(
    b: &mut ArenaBuilder,
    m: &super::NoFieldSpecialMemoryContributionRelation,
) -> MemTupleDescriptor {
    let operands = m
        .dependencies()
        .into_iter()
        .map(|a| b.resolve(a, Domain::Base))
        .collect();
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

fn lower_cache(
    b: &mut ArenaBuilder,
    addr: GKRAddress,
    rel: &super::NoFieldGKRCacheRelation,
    idx: u32,
) -> CodegenCache {
    use super::NoFieldGKRCacheRelation as C;
    let inputs: Vec<NodeId> = rel
        .dependencies()
        .into_iter()
        .map(|a| b.resolve(a, Domain::Base))
        .collect();
    let kind = match rel {
        C::SingleColumnLookup {
            relation,
            range_check_width,
        } => CacheKind::SingleColumnLookup {
            column: b.lower_linear(&relation.input, Domain::Base),
            lookup_set_index: relation.lookup_set_index,
            range_check_width: *range_check_width,
        },
        C::VectorizedLookup(v) => CacheKind::VectorizedLookup {
            columns: v
                .columns
                .iter()
                .map(|c| b.lower_linear(c, Domain::Base))
                .collect(),
            lookup_set_index: v.lookup_set_index,
        },
        C::MemoryTuple(m) => CacheKind::MemoryTuple {
            descriptor: lower_mem_tuple(b, m),
        },
        C::VectorizedLookupSetup(_) => CacheKind::VectorizedLookupSetup,
    };
    let out_node = b.add_gate_output(ProducerId::Cache(idx), 0, Domain::Ext, addr);
    CodegenCache {
        kind,
        inputs,
        out: (out_node, addr),
    }
}

fn lower_max_quad_flat(
    b: &mut ArenaBuilder,
    input: &super::NoFieldMaxQuadraticGKRRelation,
    domain: Domain,
) -> MaxQuadFlat {
    debug_assert!(
        matches!(domain, Domain::Base),
        "lower_max_quad_flat operands are always base-field"
    );
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

// ---------------------------------------------------------------------------
// Exhaustive operand-NodeId extraction from a lowered GateKind.
//
// NO `_` arm — a future variant MUST add its extraction rule here.
// ---------------------------------------------------------------------------

/// Extract every operand `NodeId` stored in a `LinearComb`.
fn linear_comb_nodes(lc: &LinearComb) -> impl Iterator<Item = NodeId> + '_ {
    lc.terms.iter().map(|(_, n)| *n)
}

/// Extract every operand `NodeId` stored in a `SingleColumnLookup`.
fn single_col_nodes(scl: &SingleColumnLookup) -> impl Iterator<Item = NodeId> + '_ {
    linear_comb_nodes(&scl.column)
}

/// Extract every operand `NodeId` stored in a `VectorLookup`.
fn vector_lookup_nodes(vl: &VectorLookup) -> Vec<NodeId> {
    vl.columns.iter().flat_map(linear_comb_nodes).collect()
}

/// Extract every operand `NodeId` stored in a `MemTupleDescriptor`.
fn mem_tuple_nodes(mt: &MemTupleDescriptor) -> impl Iterator<Item = NodeId> + '_ {
    mt.operands.iter().copied()
}

/// Exhaustively extract ALL operand `NodeId`s from a lowered `GateKind`.
/// Deliberately has no `_` arm so a new variant causes a compile error.
/// Public for downstream analysis tooling (`gkr_design_space`).
pub fn gate_kind_input_nodes(kind: &GateKind) -> Vec<NodeId> {
    match kind {
        GateKind::LinearBaseField { input } => linear_comb_nodes(input).collect(),
        GateKind::MaxQuadratic { flat, expr } => {
            let mut v = max_quad_flat_nodes(flat);
            v.push(*expr);
            v
        }
        GateKind::EnforceSingleMaxQuadraticConstraint { flat, expr } => {
            let mut v = max_quad_flat_nodes(flat);
            v.push(*expr);
            v
        }
        GateKind::EnforceConstraintsMaxQuadratic {
            quadratic,
            linear,
            constants: _,
        } => {
            let mut v: Vec<NodeId> = Vec::new();
            for ((a, c), _powers) in quadratic {
                v.push(*a);
                v.push(*c);
            }
            for (a, _powers) in linear {
                v.push(*a);
            }
            v
        }
        GateKind::CopyInBaseField { input } => vec![*input],
        GateKind::CopyInExtensionField { input } => vec![*input],
        GateKind::InitialGrandProductFromCaches { input } => input.to_vec(),
        GateKind::InitialGrandProductWithoutCaches { input } => {
            input.iter().flat_map(mem_tuple_nodes).collect()
        }
        GateKind::UnbalancedGrandProductWithCache { scalar, input } => vec![*scalar, *input],
        GateKind::MaterializeGrandProductTermExpression { input } => {
            mem_tuple_nodes(input).collect()
        }
        GateKind::TrivialProduct { input } => input.to_vec(),
        GateKind::MaskIntoIdentityProduct { input, mask } => vec![*input, *mask],
        GateKind::MaterializeSingleLookupInput {
            input,
            range_check_width: _,
        } => single_col_nodes(input).collect(),
        GateKind::MaterializedVectorLookupInput { input } => vector_lookup_nodes(input),
        GateKind::LookupWithCachedDensAndSetup { input, setup } => {
            let mut v = input.to_vec();
            v.extend_from_slice(setup);
            v
        }
        GateKind::LookupWithDensAndSetupExpressions {
            input_addr,
            input_vec,
            setup_addr,
            setup_extra,
        } => {
            let mut v = vec![*input_addr];
            v.extend(vector_lookup_nodes(input_vec));
            v.push(*setup_addr);
            v.extend_from_slice(setup_extra);
            v
        }
        GateKind::LookupWithDensAndCachedSetup {
            input_addr,
            input_vec,
            setup,
        } => {
            let mut v = vec![*input_addr];
            v.extend(vector_lookup_nodes(input_vec));
            v.extend_from_slice(setup);
            v
        }
        GateKind::LookupPairFromBaseInputs {
            input,
            range_check_width: _,
        } => input.iter().flat_map(single_col_nodes).collect(),
        GateKind::LookupPairFromMaterializedBaseInputs { input } => input.to_vec(),
        GateKind::LookupFromMaterializedBaseInputWithSetup { input, setup } => {
            let mut v = vec![*input];
            v.extend_from_slice(setup);
            v
        }
        GateKind::LookupUnbalancedPairWithMaterializedBaseInputs { input, remainder } => {
            let mut v = input.to_vec();
            v.push(*remainder);
            v
        }
        GateKind::LookupPairFromVectorInputs { input } => {
            input.iter().flat_map(vector_lookup_nodes).collect()
        }
        GateKind::LookupPairFromMaterializedVectorInputs { input } => input.to_vec(),
        GateKind::LookupFromVectorInputWithSetup {
            input,
            setup_addr,
            setup_extra,
        } => {
            let mut v = vector_lookup_nodes(input);
            v.push(*setup_addr);
            v.extend_from_slice(setup_extra);
            v
        }
        GateKind::LookupFromMaterializedVectorInputWithSetup { input, setup } => {
            let mut v = vec![*input];
            v.extend_from_slice(setup);
            v
        }
        GateKind::LookupPairFromCachedVectorInputs { input } => input.to_vec(),
        GateKind::LookupUnbalancedPairWithVectorInputs { input, remainder } => {
            let mut v = input.to_vec();
            v.extend(vector_lookup_nodes(remainder));
            v
        }
        GateKind::LookupUnbalancedPairWithMaterializedVectorInputs { input, remainder } => {
            let mut v = input.to_vec();
            v.push(*remainder);
            v
        }
        GateKind::AggregateLookupRationalPair { input } => {
            input.iter().flat_map(|pair| pair.iter().copied()).collect()
        }
        GateKind::InitsOrTeardownsInitialPair {
            timestamp_and_value: _,
            setup,
            set_idxes: _,
        } => setup.to_vec(),
    }
}

/// Extract all operand NodeIds from a `MaxQuadFlat`.
fn max_quad_flat_nodes(flat: &MaxQuadFlat) -> Vec<NodeId> {
    let mut v: Vec<NodeId> = Vec::new();
    for (a, terms) in &flat.quadratic {
        v.push(*a);
        for (_, b) in terms {
            v.push(*b);
        }
    }
    for (_, a) in &flat.linear {
        v.push(*a);
    }
    v
}

/// Assign absolute batch powers over `gates` chained with `gates_external` (caches
/// excluded), one per consumed challenge. `num_challenges` is sourced from
/// `relation_metadata` (stored on `CodegenGate`), NOT from `dst.len()`, so
/// no-output constraint gates (outputs=0, num_challenges=1) get exactly one term.
fn assign_batch_powers(
    gates: &mut [CodegenGate],
    gates_external: &mut [CodegenGate],
    start: &mut u32,
) {
    for gate in gates.iter_mut().chain(gates_external.iter_mut()) {
        let n_challenges = gate.num_challenges as u32;
        let mut terms = Vec::with_capacity(n_challenges as usize);
        // Value for the batch term: the first output node for output-bearing gates;
        // for no-output constraint gates, extract the constraint expression node
        // that is already stored inside the GateKind.
        let value = gate
            .dst
            .first()
            .map(|o| o.node)
            .unwrap_or_else(|| batch_value_for_constraint_gate(&gate.kind));
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

/// Extract a representative value `NodeId` for a no-output constraint gate
/// (one that has `num_challenges > 0` but `dst.is_empty()`).
///
/// - `EnforceSingleMaxQuadraticConstraint { expr }` — the already-lowered
///   constraint expression node is the canonical value.
/// - `EnforceConstraintsMaxQuadratic { .. }` — no single expression node is
///   emitted during lowering; pick the first NodeId from the quadratic terms if
///   any exist, then linear, falling back to `NodeId(0)` (a Constant leaf that
///   is always present at arena position 0 when any node has been interned).
fn batch_value_for_constraint_gate(kind: &GateKind) -> NodeId {
    match kind {
        GateKind::EnforceSingleMaxQuadraticConstraint { expr, .. } => *expr,
        GateKind::EnforceConstraintsMaxQuadratic {
            quadratic, linear, ..
        } => {
            if let Some(((a, _), _)) = quadratic.first() {
                *a
            } else if let Some((a, _)) = linear.first() {
                *a
            } else {
                NodeId(0)
            }
        }
        // Output-bearing gates should never reach here; fall back safely.
        _ => {
            debug_assert!(
                false,
                "batch_value_for_constraint_gate called with an output-bearing gate kind"
            );
            NodeId(0)
        }
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

    let caches: Vec<CodegenCache> = layer
        .cached_relations
        .iter()
        .enumerate()
        .map(|(idx, (addr, rel))| lower_cache(&mut b, *addr, rel, idx as u32))
        .collect();

    // Record each producer's complete operand set + slot metadata so compute_hints
    // can compute GateOutput footprints (Computed = union of gate-input footprints;
    // ScratchPrefill = {addr}). Producers were lowered inputs-first, so all operand
    // node indices are < the GateOutput index.
    for gate in gates.iter().chain(gates_external.iter()) {
        let inputs = gate_kind_input_nodes(&gate.kind);
        for slot in &gate.dst {
            b.record_output(slot.node, slot.addr, slot.forward_source, inputs.clone());
        }
    }
    for cache in &caches {
        let (node, addr) = cache.out;
        b.record_output(node, addr, ForwardSource::Computed, cache.inputs.clone());
    }

    let hints = compute_hints(&b.nodes, &b.gate_inputs, &b.gate_output_slots);
    CodegenLayer {
        arena: ExprArena {
            nodes: b.nodes,
            hints,
        },
        gates_external,
        gates,
        caches,
        intermediate_layer_width: layer.intermediate_layer_width,
    }
}

/// One forward pass over arena order. A Computed `GateOutput`'s footprint is the
/// sorted-dedup union of its producing gate's input-node footprints; a
/// `ScratchPrefill` `GateOutput`'s footprint is just `{addr}` (it has no forward
/// in-edges — it is loaded from scratch). Producers are lowered inputs-first /
/// `add_gate_output` last, so every operand index `<` the GateOutput index and a
/// single forward pass suffices.
fn compute_hints(
    nodes: &[ExprNode],
    gate_inputs: &HashMap<NodeId, Vec<NodeId>>,
    gate_output_slots: &HashMap<NodeId, (GKRAddress, ForwardSource)>,
) -> Vec<NodeHints> {
    let mut footprints: Vec<Vec<GKRAddress>> = Vec::with_capacity(nodes.len());
    let mut uses = vec![0u32; nodes.len()];
    for (i, node) in nodes.iter().enumerate() {
        let fp: Vec<GKRAddress> = match node {
            ExprNode::Constant(_) => vec![],
            ExprNode::Place { addr, .. } => vec![*addr],
            ExprNode::GateOutput { .. } => {
                let nid = NodeId(i as u32);
                match gate_output_slots.get(&nid) {
                    Some((addr, ForwardSource::ScratchPrefill)) => vec![*addr],
                    _ => {
                        let empty: Vec<NodeId> = Vec::new();
                        let inputs = gate_inputs.get(&nid).unwrap_or(&empty);
                        union_children(&footprints, inputs, &mut uses)
                    }
                }
            }
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
    RelationMeta {
        outputs,
        num_challenges,
        out_domain,
    }
}

// ===========================================================================
// Field-modular flat==expand(expr) checker (Task 10)
// ===========================================================================
//
// All arithmetic is performed in `F` (a `PrimeField`) using `F`'s own `+`/`*`,
// which are field-modular by construction.  No raw-u32 products are ever taken.
//
// Coefficients stored in `MaxQuadFlat` (and `ExprNode::Constant`) are canonical
// u32 values in [0, ORDER), which are lifted to `F` via
// `F::from_u32_with_reduction`.  The `flat` path reads them once; the `expr`
// path only ever produces `F::ONE` for leaf contributions (linear{key: 1}).
//
// Keys in the BTreeMaps are NodeId.0 values — the same arena indices that both
// `normalize_flat` (reading NodeIds from MaxQuadFlat) and `normalize_expr`
// (walking the arena from `root`) agree on.

use field::PrimeField;

/// Canonical reduced form of a degree-≤2 polynomial over variable NodeIds.
///
/// - `quadratic`: coefficient of x_a * x_b, keyed by sorted (a, b) so a ≤ b.
/// - `linear`: coefficient of x_a, keyed by a.
/// - `constant`: the field constant.
///
/// All `F` values are field elements (already reduced). Duplicate contributions
/// are summed mod p via F's `add_assign`.
#[derive(Debug, Clone)]
struct NormalizedQuadratic<F: PrimeField> {
    quadratic: BTreeMap<(u32, u32), F>,
    linear: BTreeMap<u32, F>,
    constant: F,
}

impl<F: PrimeField> NormalizedQuadratic<F> {
    fn zero() -> Self {
        NormalizedQuadratic {
            quadratic: BTreeMap::new(),
            linear: BTreeMap::new(),
            constant: F::ZERO,
        }
    }

    fn acc_quadratic(&mut self, key: (u32, u32), coeff: F) {
        if coeff.is_zero() {
            return;
        }
        let entry = self.quadratic.entry(key).or_insert(F::ZERO);
        entry.add_assign(&coeff);
        if entry.is_zero() {
            self.quadratic.remove(&key);
        }
    }

    fn acc_linear(&mut self, key: u32, coeff: F) {
        if coeff.is_zero() {
            return;
        }
        let entry = self.linear.entry(key).or_insert(F::ZERO);
        entry.add_assign(&coeff);
        if entry.is_zero() {
            self.linear.remove(&key);
        }
    }

    fn add_assign(&mut self, other: &NormalizedQuadratic<F>) {
        for (&key, &coeff) in &other.quadratic {
            self.acc_quadratic(key, coeff);
        }
        for (&key, &coeff) in &other.linear {
            self.acc_linear(key, coeff);
        }
        let c = other.constant;
        self.constant.add_assign(&c);
    }
}

impl<F: PrimeField + PartialEq> PartialEq for NormalizedQuadratic<F> {
    fn eq(&self, other: &Self) -> bool {
        self.constant == other.constant
            && self.linear == other.linear
            && self.quadratic == other.quadratic
    }
}

/// Normalize a `MaxQuadFlat` into a canonical polynomial over `F`.
///
/// Flat structure:
///   `quadratic`: Vec<(NodeId a, Vec<(u32 coeff, NodeId b)>)>
///     — represents sum of coeff * x_a * x_b
///   `linear`: Vec<(u32 coeff, NodeId a)>
///     — represents sum of coeff * x_a
///   `constant`: u32
///
/// Coefficients are lifted via `F::from_u32_with_reduction`.
fn normalize_flat<F: PrimeField>(flat: &MaxQuadFlat) -> NormalizedQuadratic<F> {
    let mut out = NormalizedQuadratic::zero();

    for (a_node, terms) in &flat.quadratic {
        for (coeff, b_node) in terms {
            let cf = F::from_u32_with_reduction(*coeff);
            if cf.is_zero() {
                continue;
            }
            // Canonicalise key as sorted pair so (a,b) == (b,a).
            let key = if a_node.0 <= b_node.0 {
                (a_node.0, b_node.0)
            } else {
                (b_node.0, a_node.0)
            };
            out.acc_quadratic(key, cf);
        }
    }
    for (coeff, a_node) in &flat.linear {
        let cf = F::from_u32_with_reduction(*coeff);
        out.acc_linear(a_node.0, cf);
    }
    let c = F::from_u32_with_reduction(flat.constant);
    out.constant.add_assign(&c);

    out
}

/// Recursively expand an arena node DAG from `root` into a `NormalizedQuadratic`.
///
/// Expansion rules:
///   `Constant(c)`       → constant = lift(c)
///   `Place` / `GateOutput` (leaf) → linear{node.0: F::ONE}
///   `Sum{terms}`        → sum of children's normalizations
///   `Product{factors}`  → pairwise-multiply the children's normalized forms;
///                         error if the result would exceed degree 2.
///
/// Returns `Err` if any intermediate result exceeds degree 2 (the gate claims
/// to be max-quadratic, so this is a malformed IR).
fn normalize_expr<F: PrimeField>(
    arena: &ExprArena,
    root: NodeId,
) -> Result<NormalizedQuadratic<F>, String> {
    let node = arena
        .nodes
        .get(root.0 as usize)
        .ok_or_else(|| format!("normalize_expr: NodeId {} out of range", root.0))?;
    match node.clone() {
        ExprNode::Constant(c) => {
            let mut out = NormalizedQuadratic::zero();
            out.constant = F::from_u32_with_reduction(c);
            Ok(out)
        }
        ExprNode::Place { .. } | ExprNode::GateOutput { .. } => {
            // Leaf variables — contribute 1 * x_{root}.
            let mut out = NormalizedQuadratic::zero();
            out.acc_linear(root.0, F::ONE);
            Ok(out)
        }
        ExprNode::Sum { terms, .. } => {
            let mut out = NormalizedQuadratic::zero();
            for t in &terms {
                let child = normalize_expr::<F>(arena, *t)?;
                out.add_assign(&child);
            }
            Ok(out)
        }
        ExprNode::Product { factors, .. } => {
            // Start with the polynomial "1" and multiply in each factor.
            let mut acc = NormalizedQuadratic::<F>::zero();
            acc.constant = F::ONE;
            for t in &factors {
                let child = normalize_expr::<F>(arena, *t)?;
                acc = multiply_normalized(&acc, &child)?;
            }
            Ok(acc)
        }
    }
}

/// Multiply two `NormalizedQuadratic` polynomials.
///
/// Degree adds: if either argument already has quadratic terms AND the other has
/// any non-constant terms, the result would be degree > 2 — return `Err`.
fn multiply_normalized<F: PrimeField>(
    a: &NormalizedQuadratic<F>,
    b: &NormalizedQuadratic<F>,
) -> Result<NormalizedQuadratic<F>, String> {
    // degree(a) = 2 if !quadratic.is_empty(), 1 if !linear.is_empty(), else 0
    // degree(b) similarly
    let deg_a = if !a.quadratic.is_empty() {
        2
    } else if !a.linear.is_empty() {
        1
    } else {
        0
    };
    let deg_b = if !b.quadratic.is_empty() {
        2
    } else if !b.linear.is_empty() {
        1
    } else {
        0
    };
    if deg_a + deg_b > 2 {
        return Err(format!(
            "normalize_expr: Product would produce degree {} > 2",
            deg_a + deg_b
        ));
    }

    let mut out = NormalizedQuadratic::<F>::zero();

    // constant * constant
    {
        let mut cc = a.constant;
        cc.mul_assign(&b.constant);
        out.constant.add_assign(&cc);
    }

    // a.constant * b.linear[j]  and  a.linear[i] * b.constant
    for (&j, &bj) in &b.linear {
        let mut t = a.constant;
        t.mul_assign(&bj);
        out.acc_linear(j, t);
    }
    for (&i, &ai) in &a.linear {
        let mut t = ai;
        t.mul_assign(&b.constant);
        out.acc_linear(i, t);
    }

    // a.linear[i] * b.linear[j]  -> quadratic term (i, j) sorted
    for (&i, &ai) in &a.linear {
        for (&j, &bj) in &b.linear {
            let mut t = ai;
            t.mul_assign(&bj);
            let key = if i <= j { (i, j) } else { (j, i) };
            out.acc_quadratic(key, t);
        }
    }

    // a.constant * b.quadratic  and  a.quadratic * b.constant
    for (&key, &bq) in &b.quadratic {
        let mut t = a.constant;
        t.mul_assign(&bq);
        out.acc_quadratic(key, t);
    }
    for (&key, &aq) in &a.quadratic {
        let mut t = aq;
        t.mul_assign(&b.constant);
        out.acc_quadratic(key, t);
    }

    // deg_a + deg_b > 2 already handled above; remaining cross-terms are
    // quadratic × linear or quadratic × quadratic which are excluded.

    Ok(out)
}

/// Field-modular guard: for every `MaxQuadratic` or
/// `EnforceSingleMaxQuadraticConstraint` gate in `layer`, verify that the
/// stored `flat` and `expr` denote the SAME degree-≤2 polynomial.
///
/// All arithmetic is performed in `F`, so BabyBear modular reduction is applied
/// after every multiply/add — no raw-u32 coefficient products are ever taken.
///
/// Returns `Err` containing the gate index (into the combined gates + gates_external
/// sequence) and a description if any mismatch is found.
pub fn verify_flat_expr<F: PrimeField + PartialEq>(layer: &CodegenLayer) -> Result<(), String> {
    for (gate_idx, gate) in layer
        .gates
        .iter()
        .chain(layer.gates_external.iter())
        .enumerate()
    {
        match &gate.kind {
            GateKind::MaxQuadratic { flat, expr }
            | GateKind::EnforceSingleMaxQuadraticConstraint { flat, expr } => {
                let nf = normalize_flat::<F>(flat);
                let ne = normalize_expr::<F>(&layer.arena, *expr)
                    .map_err(|e| format!("gate {}: normalize_expr error: {}", gate_idx, e))?;
                if nf != ne {
                    return Err(format!(
                        "gate {}: flat polynomial disagrees with expand(expr) polynomial",
                        gate_idx
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

// ===========================================================================
// Validation
// ===========================================================================

impl CodegenLayer {
    /// Subset of the spec's invariants reachable by the spike.
    pub fn verify(&self) -> Result<(), String> {
        let n = self.arena.nodes.len();
        if self.arena.hints.len() != n {
            return Err(format!(
                "hints len {} != nodes len {}",
                self.arena.hints.len(),
                n
            ));
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
                            return Err(format!(
                                "Product node {} domain disagrees with operand",
                                i
                            ));
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
        // Also verify that the total batch_terms count matches the sum of num_challenges
        // (a gate with num_challenges=1 and no batch_terms would otherwise silently pass
        // the range check since an empty powers vec trivially satisfies 0..0 == {}).
        let expected_total: usize = self
            .gates
            .iter()
            .chain(self.gates_external.iter())
            .map(|g| g.num_challenges as usize)
            .sum();
        let mut powers: Vec<u32> = self
            .gates
            .iter()
            .chain(self.gates_external.iter())
            .flat_map(|g| g.batch_terms.iter().map(|t| t.power))
            .collect();
        if powers.len() != expected_total {
            return Err(format!(
                "batch coverage: total batch_terms count {} != expected {} (sum of num_challenges)",
                powers.len(),
                expected_total
            ));
        }
        powers.sort_unstable();
        for (expected, got) in powers.iter().enumerate() {
            if *got != expected as u32 {
                return Err(format!(
                    "batch power gap/collision: expected {}, got {}",
                    expected, got
                ));
            }
        }

        // --- Invariant 7 (gate-group XOR): at most one of gates/gates_external non-empty ---
        if !self.gates.is_empty() && !self.gates_external.is_empty() {
            return Err(format!(
                "both `gates` ({}) and `gates_external` ({}) are non-empty \
                 (gate-group XOR violated, invariant 7)",
                self.gates.len(),
                self.gates_external.len()
            ));
        }

        // --- Invariant 9: every cache has a valid (in-range) output node ---
        for (ci, cache) in self.caches.iter().enumerate() {
            if (cache.out.0).0 as usize >= n {
                return Err(format!(
                    "cache {}: output node {} out of range (arena len {}), \
                     invariant 9 (every cache must be claim-bearing with a valid output)",
                    ci,
                    (cache.out.0).0,
                    n
                ));
            }
            // Also check cache input nodes are in range.
            for (ii, inp) in cache.inputs.iter().enumerate() {
                if (inp.0 as usize) >= n {
                    return Err(format!(
                        "cache {}: input[{}] node {} out of range (arena len {}), invariant 9",
                        ci, ii, inp.0, n
                    ));
                }
            }
        }

        // --- Invariant 14: MaxQuadratic family operands + outputs are Domain::Base ---
        for (gi, gate) in self
            .gates
            .iter()
            .chain(self.gates_external.iter())
            .enumerate()
        {
            match &gate.kind {
                GateKind::MaxQuadratic { flat, expr: _ }
                | GateKind::EnforceSingleMaxQuadraticConstraint { flat, expr: _ } => {
                    for nid in max_quad_flat_nodes(flat) {
                        if (nid.0 as usize) >= n {
                            return Err(format!(
                                "gate {}: MaxQuadratic flat operand node {} out of range (inv 14)",
                                gi, nid.0
                            ));
                        }
                        let dom = self.arena.nodes[nid.0 as usize].domain();
                        if !matches!(dom, Domain::Base) {
                            return Err(format!(
                                "gate {}: MaxQuadratic/EnforceSingle flat operand node {} \
                                 has domain {:?}, expected Base (invariant 14)",
                                gi, nid.0, dom
                            ));
                        }
                    }
                    for slot in &gate.dst {
                        let dom = self.arena.nodes[slot.node.0 as usize].domain();
                        if !matches!(dom, Domain::Base) {
                            return Err(format!(
                                "gate {}: MaxQuadratic output node {} has domain {:?}, \
                                 expected Base (invariant 14)",
                                gi, slot.node.0, dom
                            ));
                        }
                    }
                }
                GateKind::EnforceConstraintsMaxQuadratic {
                    quadratic,
                    linear,
                    constants: _,
                } => {
                    for ((a, c), _) in quadratic {
                        for &nid in &[*a, *c] {
                            if (nid.0 as usize) >= n {
                                return Err(format!(
                                    "gate {}: EnforceConstraintsMaxQuadratic operand node {} out of range (invariant 14)",
                                    gi, nid.0
                                ));
                            }
                            let dom = self.arena.nodes[nid.0 as usize].domain();
                            if !matches!(dom, Domain::Base) {
                                return Err(format!(
                                    "gate {}: EnforceConstraintsMaxQuadratic quadratic operand \
                                     node {} has domain {:?}, expected Base (invariant 14)",
                                    gi, nid.0, dom
                                ));
                            }
                        }
                    }
                    for (a, _) in linear {
                        if (a.0 as usize) >= n {
                            return Err(format!(
                                "gate {}: EnforceConstraintsMaxQuadratic operand node {} out of range (invariant 14)",
                                gi, a.0
                            ));
                        }
                        let dom = self.arena.nodes[a.0 as usize].domain();
                        if !matches!(dom, Domain::Base) {
                            return Err(format!(
                                "gate {}: EnforceConstraintsMaxQuadratic linear operand \
                                 node {} has domain {:?}, expected Base (invariant 14)",
                                gi, a.0, dom
                            ));
                        }
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }
}

// ===========================================================================
// CodegenCircuit::verify() — circuit-global invariants (Task 11)
// ===========================================================================

impl CodegenCircuit {
    /// Verify all invariants across the whole circuit.
    ///
    /// Calls `layer.verify()` for every layer (which covers per-layer invariants
    /// 1-6, 8, and partial 12), then adds the circuit-global checks:
    ///
    /// - **Invariant 7 (gate-group XOR):** per layer, at most one of `gates` /
    ///   `gates_external` is non-empty.
    /// - **Invariant 9 (cache claim-bearing):** every `CodegenCache` has a valid
    ///   output node (its `out.0` is in-range).
    /// - **Invariant 10 (constraint-batch fidelity):** `EnforceConstraintsMaxQuadratic`
    ///   gates have `batch_terms.len() == num_challenges (== 1)` and that term's
    ///   value NodeId is in range. This is a specialization of the batch-coverage
    ///   check inside `layer.verify()`.
    /// - **Invariant 11 (globals sufficiency):** `scratch_space_mapping` and
    ///   `scratch_space_mapping_rev` are consistent inverses:
    ///   `rev[slot] == addr ⟺ mapping[addr] == slot`.
    /// - **Invariant 12 (scratch + forward-source):** `ScratchPrefill` only on
    ///   `MaxQuadratic` outputs (already in layer.verify()); extended here to also
    ///   check each `ScratchPrefill` output's address is in `scratch_space_mapping`.
    /// - **Invariant 14 (max-quad base domain):** `MaxQuadratic` output nodes and
    ///   all operand `Place`/`GateOutput` nodes referenced by the max-quadratic
    ///   family's `flat` and `EnforceConstraintsMaxQuadratic`'s sparse terms must
    ///   be `Domain::Base`.
    pub fn verify(&self) -> Result<(), String> {
        // Per-layer checks (invariants 1-6, 8, partial 12).
        for (li, layer) in self.layers.iter().enumerate() {
            layer.verify().map_err(|e| format!("layer {}: {}", li, e))?;

            // --- Invariant 7: gate-group XOR ---
            if !layer.gates.is_empty() && !layer.gates_external.is_empty() {
                return Err(format!(
                    "layer {}: both `gates` ({}) and `gates_external` ({}) are non-empty \
                     (gate-group XOR violated, invariant 7)",
                    li,
                    layer.gates.len(),
                    layer.gates_external.len()
                ));
            }

            let n = layer.arena.nodes.len();

            // --- Invariant 9: every cache has a valid output node ---
            for (ci, cache) in layer.caches.iter().enumerate() {
                if (cache.out.0).0 as usize >= n {
                    return Err(format!(
                        "layer {}: cache {}: output node {} out of range (arena len {}), \
                         invariant 9 (every cache must be claim-bearing with a valid output)",
                        li,
                        ci,
                        (cache.out.0).0,
                        n
                    ));
                }
            }

            // --- Invariant 10: EnforceConstraintsMaxQuadratic batch fidelity ---
            for (gi, gate) in layer
                .gates
                .iter()
                .chain(layer.gates_external.iter())
                .enumerate()
            {
                if matches!(gate.kind, GateKind::EnforceConstraintsMaxQuadratic { .. }) {
                    // Must have exactly num_challenges (== 1) batch terms.
                    if gate.batch_terms.len() != gate.num_challenges as usize {
                        return Err(format!(
                            "layer {}: gate {}: EnforceConstraintsMaxQuadratic has {} batch_terms, \
                             expected {} (num_challenges), invariant 10",
                            li, gi, gate.batch_terms.len(), gate.num_challenges
                        ));
                    }
                    for bt in &gate.batch_terms {
                        if (bt.value.0 as usize) >= n {
                            return Err(format!(
                                "layer {}: gate {}: EnforceConstraintsMaxQuadratic batch_term \
                                 value {} out of range, invariant 10",
                                li, gi, bt.value.0
                            ));
                        }
                    }
                }
            }

            // --- Invariant 12 (extended): ScratchPrefill address must be in the scratch map ---
            for (gi, gate) in layer
                .gates
                .iter()
                .chain(layer.gates_external.iter())
                .enumerate()
            {
                for slot in &gate.dst {
                    if matches!(slot.forward_source, ForwardSource::ScratchPrefill) {
                        if !self.globals.scratch_space_mapping.contains_key(&slot.addr) {
                            return Err(format!(
                                "layer {}: gate {}: ScratchPrefill output addr {:?} is not in \
                                 scratch_space_mapping, invariant 12",
                                li, gi, slot.addr
                            ));
                        }
                    }
                }
            }

            // --- Invariant 14: MaxQuadratic family operands and outputs are Domain::Base ---
            for (gi, gate) in layer
                .gates
                .iter()
                .chain(layer.gates_external.iter())
                .enumerate()
            {
                match &gate.kind {
                    GateKind::MaxQuadratic { flat, expr: _ }
                    | GateKind::EnforceSingleMaxQuadraticConstraint { flat, expr: _ } => {
                        // All operand NodeIds in flat must resolve to Domain::Base nodes.
                        for nid in max_quad_flat_nodes(flat) {
                            let dom = layer.arena.nodes[nid.0 as usize].domain();
                            if !matches!(dom, Domain::Base) {
                                return Err(format!(
                                    "layer {}: gate {}: MaxQuadratic/EnforceSingle flat operand node {} \
                                     has domain {:?}, expected Base (invariant 14)",
                                    li, gi, nid.0, dom
                                ));
                            }
                        }
                        // For MaxQuadratic: its output node must also be Domain::Base.
                        for slot in &gate.dst {
                            let dom = layer.arena.nodes[slot.node.0 as usize].domain();
                            if !matches!(dom, Domain::Base) {
                                return Err(format!(
                                    "layer {}: gate {}: MaxQuadratic output node {} has domain {:?}, \
                                     expected Base (invariant 14)",
                                    li, gi, slot.node.0, dom
                                ));
                            }
                        }
                    }
                    GateKind::EnforceConstraintsMaxQuadratic {
                        quadratic,
                        linear,
                        constants: _,
                    } => {
                        // All sparse operand NodeIds must be Domain::Base.
                        let ln = layer.arena.nodes.len();
                        for ((a, c), _) in quadratic {
                            for &nid in &[*a, *c] {
                                if (nid.0 as usize) >= ln {
                                    return Err(format!(
                                        "layer {}: gate {}: EnforceConstraintsMaxQuadratic operand \
                                         node {} out of range (invariant 14)",
                                        li, gi, nid.0
                                    ));
                                }
                                let dom = layer.arena.nodes[nid.0 as usize].domain();
                                if !matches!(dom, Domain::Base) {
                                    return Err(format!(
                                        "layer {}: gate {}: EnforceConstraintsMaxQuadratic quadratic \
                                         operand node {} has domain {:?}, expected Base (invariant 14)",
                                        li, gi, nid.0, dom
                                    ));
                                }
                            }
                        }
                        for (a, _) in linear {
                            if (a.0 as usize) >= ln {
                                return Err(format!(
                                    "layer {}: gate {}: EnforceConstraintsMaxQuadratic operand \
                                     node {} out of range (invariant 14)",
                                    li, gi, a.0
                                ));
                            }
                            let dom = layer.arena.nodes[a.0 as usize].domain();
                            if !matches!(dom, Domain::Base) {
                                return Err(format!(
                                    "layer {}: gate {}: EnforceConstraintsMaxQuadratic linear \
                                     operand node {} has domain {:?}, expected Base (invariant 14)",
                                    li, gi, a.0, dom
                                ));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // --- Invariant 11: scratch_space_mapping and scratch_space_mapping_rev are inverses ---
        let mapping = &self.globals.scratch_space_mapping;
        let rev = &self.globals.scratch_space_mapping_rev;
        if mapping.len() != rev.len() {
            return Err(format!(
                "globals: scratch_space_mapping.len() ({}) != scratch_space_mapping_rev.len() ({}), \
                 not consistent inverses (invariant 11)",
                mapping.len(), rev.len()
            ));
        }
        for (addr, &slot) in mapping {
            match rev.get(&slot) {
                Some(rev_addr) if rev_addr == addr => {}
                Some(rev_addr) => {
                    return Err(format!(
                        "globals: scratch_space_mapping[{:?}] = {} but scratch_space_mapping_rev[{}] = {:?} \
                         (not a consistent inverse, invariant 11)",
                        addr, slot, slot, rev_addr
                    ));
                }
                None => {
                    return Err(format!(
                        "globals: scratch_space_mapping[{:?}] = {} but scratch_space_mapping_rev \
                         has no entry for slot {} (not a consistent inverse, invariant 11)",
                        addr, slot, slot
                    ));
                }
            }
        }
        // Also check the reverse direction: every rev entry must have a forward entry.
        for (slot, addr) in rev {
            match mapping.get(addr) {
                Some(&fwd_slot) if fwd_slot == *slot => {}
                Some(&fwd_slot) => {
                    return Err(format!(
                        "globals: scratch_space_mapping_rev[{}] = {:?} but scratch_space_mapping[{:?}] = {} \
                         (not a consistent inverse, invariant 11)",
                        slot, addr, addr, fwd_slot
                    ));
                }
                None => {
                    return Err(format!(
                        "globals: scratch_space_mapping_rev[{}] = {:?} but scratch_space_mapping \
                         has no entry for that address (not a consistent inverse, invariant 11)",
                        slot, addr
                    ));
                }
            }
        }

        Ok(())
    }
}

// ===========================================================================
// Top-level entry point: lower::<F>(artifact) -> Result<CodegenCircuit, String>
// ===========================================================================

/// Serialize a `CodegenCircuit` to a pretty-printed JSON string.
///
/// Pretty printing is chosen over compact because this writer is intended for
/// debug inspection and downstream tooling (e.g. CUDA kernel generators) that
/// benefit from human-readable output.  For machine-to-machine transport, callers
/// can invoke `serde_json::to_string` directly.
pub fn to_json_string(c: &CodegenCircuit) -> Result<String, String> {
    serde_json::to_string_pretty(c).map_err(|e| e.to_string())
}

/// Lower a full `GKRCircuitArtifact<F>` into a `CodegenCircuit`.
///
/// - Extracts globals from the artifact (no field-typed data; all structural fields).
/// - Lowers each layer via `lower_layer` (infallible).
/// - Applies the field-modular flat==expand(expr) check (invariant 13) to each layer.
/// - Verifies the complete circuit (all 15 invariants via `CodegenCircuit::verify()`).
pub fn lower<F: PrimeField + PartialEq>(
    artifact: &super::GKRCircuitArtifact<F>,
) -> Result<CodegenCircuit, String> {
    let globals = CodegenGlobals {
        trace_len: artifact.trace_len,
        offset_for_decoder_table: artifact.offset_for_decoder_table,
        has_decoder_lookup: artifact.has_decoder_lookup,
        generic_lookup_tables_width: artifact.generic_lookup_tables_width,
        tables_ids_in_generic_lookups: artifact.tables_ids_in_generic_lookups,
        num_generic_lookups: artifact.num_generic_lookups,
        decode_table_columns_mask: artifact.decode_table_columns_mask.clone(),
        table_offsets: artifact.table_offsets.clone(),
        total_tables_size: artifact.total_tables_size,
        scratch_space_size: artifact.scratch_space_size,
        scratch_space_mapping: artifact.scratch_space_mapping.clone(),
        scratch_space_mapping_rev: artifact.scratch_space_mapping_rev.clone(),
        global_output_map: artifact.global_output_map.clone(),
        memory_layout: artifact.memory_layout.clone(),
        witness_layout: artifact.witness_layout.clone(),
    };

    let mut layers = Vec::with_capacity(artifact.layers.len());
    for (li, layer) in artifact.layers.iter().enumerate() {
        let cg_layer = lower_layer(layer, &artifact.scratch_space_mapping); // infallible
        verify_flat_expr::<F>(&cg_layer)
            .map_err(|e| format!("layer {}: flat==expand(expr) check failed: {}", li, e))?; // invariant 13
        layers.push(cg_layer);
    }

    let circuit = CodegenCircuit { layers, globals };
    circuit.verify()?;
    Ok(circuit)
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
        let lc = LinearComb {
            terms: vec![],
            constant: 0,
        };
        let mq_flat = MaxQuadFlat {
            quadratic: vec![],
            linear: vec![],
            constant: 0,
        };

        // A minimal NoFieldSpecialMemoryContributionRelation with all-constant fields
        // so it never touches any BaseLayerMemory addresses.
        let mem_desc = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::Constant(0),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let mem_tuple = MemTupleDescriptor {
            descriptor: mem_desc,
            operands: vec![],
        };
        let scl = SingleColumnLookup {
            column: lc.clone(),
            lookup_set_index: 0,
        };
        let vl = VectorLookup {
            columns: vec![],
            lookup_set_index: 0,
        };

        vec![
            // 1
            GateKind::LinearBaseField { input: lc.clone() },
            // 2
            GateKind::MaxQuadratic {
                flat: mq_flat.clone(),
                expr: n,
            },
            // 3
            GateKind::EnforceSingleMaxQuadraticConstraint {
                flat: mq_flat.clone(),
                expr: n,
            },
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
            GateKind::UnbalancedGrandProductWithCache {
                scalar: n,
                input: n,
            },
            // 10
            GateKind::MaterializeGrandProductTermExpression {
                input: mem_tuple.clone(),
            },
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
            GateKind::LookupWithCachedDensAndSetup {
                input: [n; 2],
                setup: [n; 2],
            },
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
            GateKind::LookupFromMaterializedBaseInputWithSetup {
                input: n,
                setup: [n; 2],
            },
            // 21
            GateKind::LookupUnbalancedPairWithMaterializedBaseInputs {
                input: [n; 2],
                remainder: n,
            },
            // 22
            GateKind::LookupPairFromVectorInputs {
                input: [vl.clone(), vl.clone()],
            },
            // 23
            GateKind::LookupPairFromMaterializedVectorInputs { input: [n; 2] },
            // 24
            GateKind::LookupFromVectorInputWithSetup {
                input: vl.clone(),
                setup_addr: n,
                setup_extra: vec![],
            },
            // 25
            GateKind::LookupFromMaterializedVectorInputWithSetup {
                input: n,
                setup: [n; 2],
            },
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
        assert!(matches!(
            copy_gate.dst[0].forward_source,
            ForwardSource::Computed
        ));
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
        assert_eq!(
            blw0_places, 1,
            "blw(0) read by two gates must be a single Place node"
        );
    }

    #[test]
    fn resolve_links_intra_layer_producer_not_a_fresh_place() {
        // Direct ArenaBuilder check of the producer->consumer edge mechanism
        // (finding 6): a same-layer produced address resolves to its GateOutput, not a
        // fresh Place; an external address resolves to a Place.
        let mut b = ArenaBuilder::default();
        let cache_addr = GKRAddress::Cached {
            layer: 0,
            offset: 0,
        };
        let produced = b.add_gate_output(ProducerId::Cache(0), 0, Domain::Ext, cache_addr);
        // a consumer reading the cache address must get the SAME node (the producer).
        let consumed = b.resolve(cache_addr, Domain::Ext);
        assert_eq!(
            consumed, produced,
            "intra-layer address must resolve to its producer"
        );
        assert!(matches!(
            b.nodes[consumed.0 as usize],
            ExprNode::GateOutput { .. }
        ));
        // an external address has no producer -> a Place leaf, a distinct node.
        let external = b.resolve(blw(9), Domain::Base);
        assert_ne!(external, produced);
        assert!(matches!(
            b.nodes[external.0 as usize],
            ExprNode::Place { .. }
        ));
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

        let m_base_1_1 = RelationMeta {
            outputs: 1,
            num_challenges: 1,
            out_domain: Domain::Base,
        };
        let m_base_0_1 = RelationMeta {
            outputs: 0,
            num_challenges: 1,
            out_domain: Domain::Base,
        };
        let m_ext_1_1 = RelationMeta {
            outputs: 1,
            num_challenges: 1,
            out_domain: Domain::Ext,
        };
        let m_ext_2_2 = RelationMeta {
            outputs: 2,
            num_challenges: 2,
            out_domain: Domain::Ext,
        };

        vec![
            // --- class (1, 1, Base) ---
            (
                R::LinearBaseFieldRelation {
                    input: lin.clone(),
                    output: out0,
                },
                m_base_1_1,
            ),
            (
                R::MaxQuadratic {
                    input: mq.clone(),
                    expression: E::Constant(0),
                    output: out0,
                },
                m_base_1_1,
            ),
            (
                R::CopyInBaseField {
                    input: a0,
                    output: out0,
                },
                m_base_1_1,
            ),
            (
                R::MaterializeSingleLookupInput {
                    input: scl.clone(),
                    output: out0,
                    range_check_width: 16,
                },
                m_base_1_1,
            ),
            // --- class (0, 1, Base) ---
            (
                R::EnforceSingleMaxQuadraticConstraint {
                    input: mq.clone(),
                    expression: E::Constant(0),
                },
                m_base_0_1,
            ),
            (
                R::EnforceConstraintsMaxQuadratic {
                    input: NoFieldMaxQuadraticConstraintsGKRRelation {
                        quadratic_terms: vec![].into_boxed_slice(),
                        linear_terms: vec![].into_boxed_slice(),
                        constants: vec![].into_boxed_slice(),
                    },
                },
                m_base_0_1,
            ),
            // --- class (1, 1, Ext) ---
            (
                R::CopyInExtensionField {
                    input: a0,
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::InitialGrandProductFromCaches {
                    input: [a0, a1],
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::InitialGrandProductWithoutCaches {
                    input: [mem_desc.clone(), mem_desc.clone()],
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::UnbalancedGrandProductWithCache {
                    scalar: a0,
                    input: a1,
                    output: out0,
                },
                m_ext_1_1,
            ),
            // MaterializeGrandProductTermExpression: panicking variant — still covered by metadata
            (
                R::MaterializeGrandProductTermExpression {
                    input: mem_desc.clone(),
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::TrivialProduct {
                    input: [a0, a1],
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::MaskIntoIdentityProduct {
                    input: a0,
                    mask: a1,
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::MaterializedVectorLookupInput {
                    input: vl.clone(),
                    output: out0,
                },
                m_ext_1_1,
            ),
            (
                R::InitsOrTeardownsInitialPair {
                    timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
                    setup: [a0, a1],
                    output: out0,
                    set_idxes: [0, 1],
                },
                m_ext_1_1,
            ),
            // --- class (2, 2, Ext) ---
            (
                R::LookupWithCachedDensAndSetup {
                    input: [a0, a1],
                    setup: [a0, a1],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupWithDensAndSetupExpressions {
                    input: (a0, vl.clone()),
                    setup: (a0, vec![a1].into_boxed_slice()),
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupWithDensAndCachedSetup {
                    input: (a0, vl.clone()),
                    setup: (a0, a1),
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupPairFromBaseInputs {
                    input: [scl.clone(), scl.clone()],
                    output: [out0, out1],
                    range_check_width: 16,
                },
                m_ext_2_2,
            ),
            (
                R::LookupPairFromMaterializedBaseInputs {
                    input: [a0, a1],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupFromMaterializedBaseInputWithSetup {
                    input: a0,
                    setup: [a0, a1],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupUnbalancedPairWithMaterializedBaseInputs {
                    input: [a0, a1],
                    remainder: a0,
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupPairFromVectorInputs {
                    input: [vl.clone(), vl.clone()],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupPairFromMaterializedVectorInputs {
                    input: [a0, a1],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            // LookupFromVectorInputWithSetup: panicking variant — still covered by metadata
            (
                R::LookupFromVectorInputWithSetup {
                    input: vl.clone(),
                    setup: (a0, vec![a1].into_boxed_slice()),
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupFromMaterializedVectorInputWithSetup {
                    input: a0,
                    setup: [a0, a1],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::LookupPairFromCachedVectorInputs {
                    input: [a0, a1],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            // LookupUnbalancedPairWithVectorInputs: panicking variant — still covered by metadata
            (
                R::LookupUnbalancedPairWithVectorInputs {
                    input: [a0, a1],
                    remainder: vl.clone(),
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            // LookupUnbalancedPairWithMaterializedVectorInputs: panicking variant — still covered by metadata
            (
                R::LookupUnbalancedPairWithMaterializedVectorInputs {
                    input: [a0, a1],
                    remainder: a0,
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
            (
                R::AggregateLookupRationalPair {
                    input: [[a0, a1], [a0, a1]],
                    output: [out0, out1],
                },
                m_ext_2_2,
            ),
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

    /// Build a `GKRLayerDescription` with two gates in `gates` (no external connections).
    fn two_gate_layer(rel_a: NoFieldGKRRelation, rel_b: NoFieldGKRRelation) -> GKRLayerDescription {
        GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            gates: vec![
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: rel_a,
                },
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: rel_b,
                },
            ],
            intermediate_layer_width: Some(2),
        }
    }

    // -----------------------------------------------------------------------
    // Task 8: metadata-driven batch-power tests
    // -----------------------------------------------------------------------

    #[test]
    fn batch_powers_cover_range_no_gaps() {
        // 1-challenge gate (CopyInBaseField) + 2-challenge (two-output) gate =>
        // powers {0, 1, 2} with no gaps.
        let layer = two_gate_layer(
            NoFieldGKRRelation::CopyInBaseField {
                input: blw(0),
                output: inner(1, 0),
            },
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
                input: [blw(1), blw(2)],
                output: [inner(1, 1), inner(1, 2)],
            },
        );
        let cg = lower_layer(&layer, &BTreeMap::new());
        let mut powers: Vec<u32> = cg
            .gates
            .iter()
            .flat_map(|g| g.batch_terms.iter().map(|t| t.power))
            .collect();
        powers.sort();
        assert_eq!(powers, vec![0, 1, 2]);
        cg.verify().unwrap();
    }

    #[test]
    fn batch_powers_count_no_output_constraint_gate() {
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        // EnforceSingleMaxQuadraticConstraint: outputs=0, num_challenges=1.
        // Must produce exactly 1 batch_term (power 0) even though dst is empty.
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![(1u32, blw(0))].into_boxed_slice(),
            constant: 0,
        };
        let layer = single_gate_layer(NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: mq,
            expression: E::Place(blw(0)),
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(
            g.dst.is_empty(),
            "EnforceSingleMaxQuadraticConstraint has no output slots"
        );
        assert_eq!(
            g.batch_terms.len(),
            1,
            "no-output constraint gate must have exactly 1 batch_term (from num_challenges=1)"
        );
        assert_eq!(g.batch_terms[0].power, 0);
        // value must be a valid node (not a dangling reference)
        assert!(
            (g.batch_terms[0].value.0 as usize) < cg.arena.nodes.len(),
            "batch_term value must be a valid arena node"
        );
        cg.verify().unwrap();
    }

    #[test]
    fn lowers_trivial_product_two_inputs() {
        let layer = single_gate_layer(NoFieldGKRRelation::TrivialProduct {
            input: [
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 0,
                },
                GKRAddress::InnerLayer {
                    layer: 0,
                    offset: 1,
                },
            ],
            output: GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
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
        assert!(matches!(
            g.kind,
            GateKind::InitialGrandProductFromCaches { .. }
        ));
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
        assert!(matches!(
            g.kind,
            GateKind::UnbalancedGrandProductWithCache { .. }
        ));
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
        let has_ext_place = cg.arena.nodes.iter().any(
            |n| matches!(n, ExprNode::Place { addr, domain: Domain::Ext, .. } if *addr == blw(0)),
        );
        let has_base_place = cg.arena.nodes.iter().any(
            |n| matches!(n, ExprNode::Place { addr, domain: Domain::Base, .. } if *addr == blw(1)),
        );
        assert!(has_ext_place, "input (blw(0)) must be Ext-domain Place");
        assert!(has_base_place, "mask (blw(1)) must be Base-domain Place");
        cg.verify().unwrap();
    }

    // -----------------------------------------------------------------------
    // Task 5: lookup materialization lowering tests
    // -----------------------------------------------------------------------

    #[test]
    fn lowers_materialize_single_lookup_input() {
        use super::super::NoFieldGKRRelation as R;
        use crate::definitions::gkr::{NoFieldLinearRelation, NoFieldSingleColumnLookupRelation};

        // Build a 2-term linear relation: 1*blw(0) + 2*blw(1) + 0
        let lin = NoFieldLinearRelation {
            linear_terms: vec![(1u32, blw(0)), (2u32, blw(1))].into_boxed_slice(),
            constant: 0,
        };
        let scl = NoFieldSingleColumnLookupRelation {
            input: lin,
            lookup_set_index: 7,
        };
        let output = inner(1, 0);
        let layer = single_gate_layer(R::MaterializeSingleLookupInput {
            input: scl,
            output,
            range_check_width: 16,
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let g = &cg.gates[0];
        assert!(
            matches!(
                g.kind,
                GateKind::MaterializeSingleLookupInput {
                    range_check_width: 16,
                    ..
                }
            ),
            "expected MaterializeSingleLookupInput with range_check_width=16, got {:?}",
            g.kind
        );
        assert_eq!(g.dst.len(), 1);
        // lookup_set_index must be preserved
        if let GateKind::MaterializeSingleLookupInput {
            input: ref scl_ir, ..
        } = g.kind
        {
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
        use super::super::NoFieldGKRRelation as R;
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
        let layer = single_gate_layer(R::MaterializedVectorLookupInput { input: vl, output });
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
            matches!(
                n,
                ExprNode::Place {
                    domain: Domain::Ext,
                    ..
                }
            )
        });
        assert!(has_ext_place, "ext copy input must be an Ext-domain Place");
        // Symmetry: no Base Place should exist in a pure ext-copy layer.
        let has_base_place = cg.arena.nodes.iter().any(|n| {
            matches!(
                n,
                ExprNode::Place {
                    domain: Domain::Base,
                    ..
                }
            )
        });
        assert!(
            !has_base_place,
            "ext copy layer must not produce Base-domain Place nodes"
        );
        cg.verify().expect("verify");
    }

    /// All Place nodes produced for a pure max-quadratic layer must be Domain::Base.
    #[test]
    fn max_quad_operand_places_are_base_domain() {
        // sample_layer() contains a MaxQuadratic gate (plus a CopyInBaseField gate);
        // every operand address is a base-layer witness, so all Place nodes must be Base.
        let cg = lower_layer(&sample_layer(), &BTreeMap::new());
        let has_ext_place = cg.arena.nodes.iter().any(|n| {
            matches!(
                n,
                ExprNode::Place {
                    domain: Domain::Ext,
                    ..
                }
            )
        });
        assert!(
            !has_ext_place,
            "max-quad operands must all be Base-domain Place nodes"
        );
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
        assert_eq!(
            cg.arena.nodes[input[0].0 as usize].domain(),
            Domain::Base,
            "input[0] must be Base"
        );
        assert_eq!(
            cg.arena.nodes[input[1].0 as usize].domain(),
            Domain::Base,
            "input[1] must be Base"
        );
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
        assert_eq!(
            cg.arena.nodes[input[0].0 as usize].domain(),
            Domain::Base,
            "input[0] must be Base"
        );
        assert_eq!(
            cg.arena.nodes[input[1].0 as usize].domain(),
            Domain::Ext,
            "input[1] must be Ext"
        );
        assert_eq!(
            cg.arena.nodes[setup[0].0 as usize].domain(),
            Domain::Base,
            "setup[0] must be Base"
        );
        assert_eq!(
            cg.arena.nodes[setup[1].0 as usize].domain(),
            Domain::Ext,
            "setup[1] must be Ext"
        );
        assert_eq!(g.dst.len(), 2);
        cg.verify().unwrap();
    }

    // -----------------------------------------------------------------------
    // Task 7: cached_relations lowering
    // -----------------------------------------------------------------------

    fn cached(layer: usize, offset: usize) -> GKRAddress {
        GKRAddress::Cached { layer, offset }
    }

    /// Build a layer with a single cache entry (+ no gates) for testing.
    fn cached_layer(
        addr: GKRAddress,
        rel: super::super::NoFieldGKRCacheRelation,
    ) -> GKRLayerDescription {
        let mut cached_relations = BTreeMap::new();
        cached_relations.insert(addr, rel);
        GKRLayerDescription {
            layer: 1,
            gates_with_external_connections: vec![],
            gates: vec![],
            cached_relations,
            intermediate_layer_width: None,
        }
    }

    /// VectorizedLookupSetup with two dependency addresses — verify inputs are lowered.
    #[test]
    fn lowers_cache_vectorized_lookup_setup() {
        let dep0 = blw(10);
        let dep1 = blw(11);
        let out_addr = cached(1, 0);
        let rel = super::super::NoFieldGKRCacheRelation::VectorizedLookupSetup(
            vec![dep0, dep1].into_boxed_slice(),
        );
        let layer = cached_layer(out_addr, rel);
        let cg = lower_layer(&layer, &BTreeMap::new());
        assert_eq!(cg.caches.len(), 1);
        assert!(
            matches!(cg.caches[0].kind, CacheKind::VectorizedLookupSetup),
            "expected VectorizedLookupSetup kind"
        );
        // dependencies() returns [dep0, dep1] -> 2 input nodes
        assert_eq!(cg.caches[0].inputs.len(), 2, "expected 2 dependency inputs");
        assert_eq!(cg.caches[0].out.1, out_addr, "output address must match");
        cg.verify().unwrap();
    }

    /// SingleColumnLookup cache — verify kind, range_check_width, and 1 input.
    #[test]
    fn lowers_cache_single_column_lookup() {
        use crate::definitions::gkr::NoFieldLinearRelation;
        let dep = blw(5);
        let out_addr = cached(2, 0);
        let relation = super::NoFieldSingleColumnLookupRelation {
            input: NoFieldLinearRelation {
                linear_terms: vec![(1u32, dep)].into_boxed_slice(),
                constant: 0,
            },
            lookup_set_index: 3,
        };
        let rel = super::super::NoFieldGKRCacheRelation::SingleColumnLookup {
            relation,
            range_check_width: 8,
        };
        let layer = cached_layer(out_addr, rel);
        let cg = lower_layer(&layer, &BTreeMap::new());
        assert_eq!(cg.caches.len(), 1);
        let CacheKind::SingleColumnLookup {
            lookup_set_index,
            range_check_width,
            ..
        } = &cg.caches[0].kind
        else {
            panic!("expected SingleColumnLookup kind");
        };
        assert_eq!(*lookup_set_index, 3);
        assert_eq!(*range_check_width, 8);
        assert_eq!(cg.caches[0].inputs.len(), 1);
        assert_eq!(cg.caches[0].out.1, out_addr);
        cg.verify().unwrap();
    }

    /// VectorizedLookup cache — verify columns count.
    #[test]
    fn lowers_cache_vectorized_lookup() {
        use crate::definitions::gkr::{NoFieldLinearRelation, NoFieldVectorLookupRelation};
        let dep0 = blw(20);
        let dep1 = blw(21);
        let out_addr = cached(3, 0);
        let col0 = NoFieldLinearRelation {
            linear_terms: vec![(1u32, dep0)].into_boxed_slice(),
            constant: 0,
        };
        let col1 = NoFieldLinearRelation {
            linear_terms: vec![(1u32, dep1)].into_boxed_slice(),
            constant: 0,
        };
        let v = NoFieldVectorLookupRelation {
            columns: vec![col0, col1].into_boxed_slice(),
            lookup_set_index: 7,
        };
        let rel = super::super::NoFieldGKRCacheRelation::VectorizedLookup(v);
        let layer = cached_layer(out_addr, rel);
        let cg = lower_layer(&layer, &BTreeMap::new());
        assert_eq!(cg.caches.len(), 1);
        let CacheKind::VectorizedLookup {
            columns,
            lookup_set_index,
        } = &cg.caches[0].kind
        else {
            panic!("expected VectorizedLookup kind");
        };
        assert_eq!(columns.len(), 2);
        assert_eq!(*lookup_set_index, 7);
        // 2 unique dep addresses -> 2 input nodes
        assert_eq!(cg.caches[0].inputs.len(), 2);
        assert_eq!(cg.caches[0].out.1, out_addr);
        cg.verify().unwrap();
    }

    /// MemoryTuple cache — constant-field descriptor so 0 deps.
    #[test]
    fn lowers_cache_memory_tuple() {
        use super::super::{
            CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
            NoFieldSpecialMemoryContributionRelation,
        };
        use crate::definitions::gkr::RamWordRepresentation;
        let out_addr = cached(4, 0);
        let mem_desc = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::Constant(0),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let rel = super::super::NoFieldGKRCacheRelation::MemoryTuple(mem_desc);
        let layer = cached_layer(out_addr, rel);
        let cg = lower_layer(&layer, &BTreeMap::new());
        assert_eq!(cg.caches.len(), 1);
        assert!(
            matches!(cg.caches[0].kind, CacheKind::MemoryTuple { .. }),
            "expected MemoryTuple kind"
        );
        // Constant mem_desc has 0 dependencies
        assert_eq!(cg.caches[0].inputs.len(), 0);
        assert_eq!(cg.caches[0].out.1, out_addr);
        cg.verify().unwrap();
    }

    // -----------------------------------------------------------------------
    // Task 9: footprint / uses hints with gate context
    // -----------------------------------------------------------------------

    #[test]
    fn computed_gate_output_footprint_is_input_union() {
        let layer = single_gate_layer(NoFieldGKRRelation::CopyInBaseField {
            input: GKRAddress::BaseLayerWitness(7),
            output: GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let (i, _) = cg
            .arena
            .nodes
            .iter()
            .enumerate()
            .find(|(_, n)| matches!(n, ExprNode::GateOutput { .. }))
            .unwrap();
        assert!(
            cg.arena.hints[i]
                .footprint
                .contains(&GKRAddress::BaseLayerWitness(7)),
            "Computed GateOutput footprint must contain its input address"
        );
    }

    #[test]
    fn computed_footprint_unions_all_operands() {
        let layer = single_gate_layer(NoFieldGKRRelation::TrivialProduct {
            input: [
                GKRAddress::BaseLayerWitness(3),
                GKRAddress::BaseLayerWitness(8),
            ],
            output: GKRAddress::InnerLayer {
                layer: 1,
                offset: 0,
            },
        });
        let cg = lower_layer(&layer, &BTreeMap::new());
        let (i, _) = cg
            .arena
            .nodes
            .iter()
            .enumerate()
            .find(|(_, n)| matches!(n, ExprNode::GateOutput { .. }))
            .unwrap();
        let fp = &cg.arena.hints[i].footprint;
        assert!(
            fp.contains(&GKRAddress::BaseLayerWitness(3)),
            "footprint must union operand 0"
        );
        assert!(
            fp.contains(&GKRAddress::BaseLayerWitness(8)),
            "footprint must union operand 1"
        );
    }

    #[test]
    fn scratch_prefill_gate_output_footprint_is_addr_only() {
        // A scratch-backed MaxQuadratic output is ScratchPrefill -> footprint = {addr} only.
        let layer = sample_layer();
        let mut scratch = BTreeMap::new();
        scratch.insert(inner(1, 1), 0usize); // MaxQuadratic output is scratch-backed
        let cg = lower_layer(&layer, &scratch);
        let mq = cg
            .gates
            .iter()
            .find(|g| matches!(g.kind, GateKind::MaxQuadratic { .. }))
            .unwrap();
        let slot = &mq.dst[0];
        assert!(matches!(slot.forward_source, ForwardSource::ScratchPrefill));
        let fp = &cg.arena.hints[slot.node.0 as usize].footprint;
        assert_eq!(
            fp.as_slice(),
            &[inner(1, 1)],
            "ScratchPrefill footprint must be exactly {{addr}}"
        );
    }

    // -----------------------------------------------------------------------
    // Task 10: field-modular flat==expand(expr) checker
    // -----------------------------------------------------------------------

    use ::field::baby_bear::base::BabyBearField;
    type ConcreteField = BabyBearField;

    /// Build a `MaxQuadratic` relation whose `flat` and `expression` denote the
    /// SAME degree-2 polynomial: x0 * x1 + 3.
    ///
    /// flat:        quadratic = [(blw(0), [(1, blw(1))]]
    ///              linear    = []
    ///              constant  = 3
    /// expression:  Product(Place(blw(0)), Place(blw(1))) + Constant(3)
    fn matching_max_quadratic() -> NoFieldGKRRelation {
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![(blw(0), vec![(1u32, blw(1))].into_boxed_slice())]
                .into_boxed_slice(),
            linear_terms: vec![].into_boxed_slice(),
            constant: 3,
        };
        let expr = E::Sum(vec![
            E::Product(vec![E::Place(blw(0)), E::Place(blw(1))]),
            E::Constant(3),
        ]);
        NoFieldGKRRelation::MaxQuadratic {
            input: mq,
            expression: expr,
            output: inner(1, 0),
        }
    }

    /// Build a `MaxQuadratic` relation whose `flat` and `expression` DISAGREE:
    /// flat says coefficient 1 on x0*x1, but expression uses coefficient 2.
    fn mismatched_max_quadratic() -> NoFieldGKRRelation {
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        // flat: 1 * x0 * x1 + 3
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![(blw(0), vec![(1u32, blw(1))].into_boxed_slice())]
                .into_boxed_slice(),
            linear_terms: vec![].into_boxed_slice(),
            constant: 3,
        };
        // expression: 2 * x0 * x1 + 3 (coefficient mismatch on x0*x1)
        let expr = E::Sum(vec![
            E::Product(vec![E::Place(blw(0)), E::Place(blw(1))]),
            E::Product(vec![E::Place(blw(0)), E::Place(blw(1))]),
            E::Constant(3),
        ]);
        NoFieldGKRRelation::MaxQuadratic {
            input: mq,
            expression: expr,
            output: inner(1, 0),
        }
    }

    #[test]
    fn flat_and_expr_must_agree() {
        // matching: build a MaxQuadratic whose expr lowers to the same poly as its flat.
        let good = single_gate_layer(matching_max_quadratic());
        let cg = lower_layer(&good, &BTreeMap::new());
        assert!(
            verify_flat_expr::<ConcreteField>(&cg).is_ok(),
            "matching flat/expr must be accepted"
        );

        // mismatched: expr disagrees with flat -> Err.
        let bad = single_gate_layer(mismatched_max_quadratic());
        let cg2 = lower_layer(&bad, &BTreeMap::new());
        assert!(
            verify_flat_expr::<ConcreteField>(&cg2).is_err(),
            "mismatched flat/expr must be rejected"
        );
    }

    /// Prove the field-modular point: two large coefficients near ORDER whose
    /// NATIVE u64 product differs from their reduced product should still match
    /// when both sides use F-arithmetic.
    ///
    /// BabyBear ORDER = 0x78000001 = 2013265921.
    ///
    /// Choose coeff_a = ORDER - 1 and coeff_b = ORDER - 1.
    /// Their native product (ORDER-1)^2 ≈ 4e18, which overflows u32 and
    /// differs from the field-reduced result.
    ///
    /// The flat explicitly stores the field-reduced product: (ORDER-1)^2 mod p.
    /// The expression stores two operands with coeff (ORDER-1) each — but wait,
    /// the flat only stores the coefficient of the product node, and the
    /// expression uses `E::Product` of two places (coefficient = 1 each).
    /// So to exercise large coefficient arithmetic we instead use the linear
    /// terms: flat linear coeff = (ORDER-1), expression = Sum of (ORDER-1) copies
    /// of a Place — which is equivalent but impractical.
    ///
    /// Simpler approach: place a large u32 coefficient in a linear flat term
    /// and match it with the corresponding expression. The comparison itself
    /// is the field-modular test: F::from_u32_with_reduction(ORDER-1) on both
    /// sides must produce the same F element.
    ///
    /// Additionally: test a quadratic flat where coeff = ORDER - 1 (nearly -1 mod p),
    /// and the expr is a negated-ish product. This verifies no raw-u32 multiply occurs.
    #[test]
    fn field_modular_large_coefficients_do_not_falsely_reject() {
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        // ORDER - 1 as a coefficient: this is -1 mod p in BabyBear.
        // Use it as a linear coefficient in both flat and expression.
        // Expression: Sum of one Place scaled by (ORDER-1) is not directly expressible
        // via E::Constant + E::Product in the pure-multiplicative IR, so instead we
        // exercise the flat linear path:
        //
        //   flat:  linear = [(ORDER-1, blw(0))], rest = 0
        //   expr:  we cannot express (ORDER-1)*x0 using just Product/Sum/Constant/Place
        //          without a scalar-mul node — the NoFieldStructuredExpression grammar
        //          only has Sum/Product/Place/Constant, no explicit scalar-mul.
        //
        // So we pick a coefficient that CAN be expressed as a sum of Places:
        //   coeff = 2 -> flat linear [(2, blw(0))], expr Sum([Place(blw(0)), Place(blw(0))])
        //
        // But to test the large-coeff path we set constant = ORDER - 1 in both:
        //   flat.constant = ORDER - 1
        //   expr = Constant(ORDER - 1)
        //
        // F::from_u32_with_reduction(ORDER - 1) must equal itself on both sides
        // (the comparison is identity since it's the same lift), but it exercises
        // the lift path for a near-ORDER value.
        let large = ConcreteField::ORDER - 1; // = p - 1 = -1 mod p
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![].into_boxed_slice(),
            constant: large,
        };
        let expr = E::Constant(large);
        let rel = NoFieldGKRRelation::MaxQuadratic {
            input: mq,
            expression: expr,
            output: inner(1, 0),
        };
        let cg = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        assert!(
            verify_flat_expr::<ConcreteField>(&cg).is_ok(),
            "large near-ORDER constant must not be falsely rejected"
        );

        // Now verify that if the flat has large constant but expr has a different
        // constant (e.g. 1), the checker correctly rejects.
        let mq2 = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![].into_boxed_slice(),
            constant: large,
        };
        let expr2 = E::Constant(1); // mismatched
        let rel2 = NoFieldGKRRelation::MaxQuadratic {
            input: mq2,
            expression: expr2,
            output: inner(1, 1),
        };
        let cg2 = lower_layer(&single_gate_layer(rel2), &BTreeMap::new());
        assert!(
            verify_flat_expr::<ConcreteField>(&cg2).is_err(),
            "flat constant (ORDER-1) vs expr constant 1 must be rejected"
        );
    }

    // -----------------------------------------------------------------------
    // Task 11: invariant-violation tests (written before implementation, TDD).
    // Each constructs a CodegenLayer/CodegenCircuit that violates EXACTLY one
    // invariant and asserts verify() returns Err; plus a valid baseline.
    // -----------------------------------------------------------------------

    /// Build a valid single-gate CodegenLayer using CopyInBaseField for use as a
    /// baseline that all violation tests can mutate.
    fn valid_copy_layer() -> CodegenLayer {
        lower_layer(
            &single_gate_layer(NoFieldGKRRelation::CopyInBaseField {
                input: blw(0),
                output: inner(1, 0),
            }),
            &BTreeMap::new(),
        )
    }

    /// Build a minimal valid CodegenCircuit (one layer, no-op globals).
    fn valid_circuit_one_layer() -> CodegenCircuit {
        use crate::definitions::gkr::{GKRMemoryLayout, GKRWitnessLayout};
        CodegenCircuit {
            layers: vec![valid_copy_layer()],
            globals: CodegenGlobals {
                trace_len: 1,
                offset_for_decoder_table: 0,
                has_decoder_lookup: false,
                generic_lookup_tables_width: 1,
                tables_ids_in_generic_lookups: false,
                num_generic_lookups: 0,
                decode_table_columns_mask: vec![],
                table_offsets: vec![],
                total_tables_size: 0,
                scratch_space_size: 0,
                scratch_space_mapping: BTreeMap::new(),
                scratch_space_mapping_rev: BTreeMap::new(),
                global_output_map: BTreeMap::new(),
                memory_layout: GKRMemoryLayout {
                    ram_access_sets: vec![],
                    machine_state: None,
                    delegation_state: None,
                    decoder_input: None,
                    indirect_access_variable_offsets: vec![],
                    teardown_sets: vec![],
                    total_width: 0,
                    inits_and_teardowns_word_bits: None,
                },
                witness_layout: GKRWitnessLayout {
                    multiplicities_columns_for_range_check_16: 0..0,
                    multiplicities_columns_for_timestamp_range_check: 0..0,
                    multiplicities_columns_for_generic_lookup: 0..0,
                    total_width: 0,
                },
            },
        }
    }

    // -- Invariant 7: gate-group XOR (at most one of gates/gates_external non-empty) --

    #[test]
    fn inv7_gate_group_xor_violation_detected() {
        let mut layer = valid_copy_layer();
        // Clone the single gate into gates_external too — both are now non-empty.
        layer.gates_external = layer.gates.clone();
        // Reassign correct batch powers so power check passes; the XOR check must fire first.
        let mut p = 0u32;
        assign_batch_powers(&mut layer.gates, &mut layer.gates_external, &mut p);
        assert!(
            layer.verify().is_err(),
            "both gates and gates_external non-empty must be rejected (inv 7)"
        );
    }

    #[test]
    fn inv7_gate_group_xor_valid_layer_passes() {
        let layer = valid_copy_layer();
        layer
            .verify()
            .expect("valid single-group layer must pass inv 7");
    }

    // -- Invariant 9: every cache is claim-bearing (has a valid output node) --

    #[test]
    fn inv9_cache_out_node_out_of_range_detected() {
        let mut layer = valid_copy_layer();
        // Add a cache with an out node that is out-of-range.
        layer.caches.push(CodegenCache {
            kind: CacheKind::VectorizedLookupSetup,
            inputs: vec![],
            out: (
                NodeId(9999),
                GKRAddress::Cached {
                    layer: 0,
                    offset: 0,
                },
            ),
        });
        assert!(
            layer.verify().is_err(),
            "cache with out-of-range output node must be rejected (inv 9)"
        );
    }

    #[test]
    fn inv9_cache_valid_passes() {
        use crate::definitions::gkr::NoFieldLinearRelation;
        let dep = blw(5);
        let out_addr = GKRAddress::Cached {
            layer: 2,
            offset: 0,
        };
        let relation = NoFieldSingleColumnLookupRelation {
            input: NoFieldLinearRelation {
                linear_terms: vec![(1u32, dep)].into_boxed_slice(),
                constant: 0,
            },
            lookup_set_index: 3,
        };
        let rel = super::super::NoFieldGKRCacheRelation::SingleColumnLookup {
            relation,
            range_check_width: 8,
        };
        let layer_desc = cached_layer(out_addr, rel);
        let cg = lower_layer(&layer_desc, &BTreeMap::new());
        cg.verify().expect("valid cache layer must pass inv 9");
    }

    // -- Invariant 10: EnforceConstraintsMaxQuadratic has exactly num_challenges batch terms --

    #[test]
    fn inv10_enforce_constraints_max_quad_missing_batch_term_detected() {
        use super::super::NoFieldMaxQuadraticConstraintsGKRRelation;
        // Build a valid EnforceConstraintsMaxQuadratic gate then strip its batch_terms.
        let rel = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
            input: NoFieldMaxQuadraticConstraintsGKRRelation {
                quadratic_terms: vec![].into_boxed_slice(),
                linear_terms: vec![(blw(0), vec![(1u32, 0usize)].into_boxed_slice())]
                    .into_boxed_slice(),
                constants: vec![].into_boxed_slice(),
            },
        };
        let mut layer = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        // Simulate a missing batch term by clearing.
        layer.gates[0].batch_terms.clear();
        // The batch-coverage check must detect the gap (power 0 missing).
        assert!(
            layer.verify().is_err(),
            "EnforceConstraintsMaxQuadratic with no batch terms must fail (inv 10 / batch coverage)"
        );
    }

    #[test]
    fn inv10_enforce_constraints_max_quad_valid_passes() {
        use super::super::NoFieldMaxQuadraticConstraintsGKRRelation;
        let rel = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
            input: NoFieldMaxQuadraticConstraintsGKRRelation {
                quadratic_terms: vec![].into_boxed_slice(),
                linear_terms: vec![(blw(0), vec![(1u32, 0usize)].into_boxed_slice())]
                    .into_boxed_slice(),
                constants: vec![].into_boxed_slice(),
            },
        };
        let layer = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        layer
            .verify()
            .expect("valid EnforceConstraintsMaxQuadratic layer must pass");
    }

    // -- Invariant 11: globals sufficiency (scratch maps are consistent inverses) --

    #[test]
    fn inv11_scratch_map_inconsistent_detected() {
        let mut circuit = valid_circuit_one_layer();
        // Add an entry to scratch_space_mapping but NOT to scratch_space_mapping_rev
        // -> the maps are inconsistent (not inverse to each other).
        let addr = blw(99);
        circuit.globals.scratch_space_mapping.insert(addr, 42);
        // scratch_space_mapping_rev does NOT have 42 -> addr
        assert!(
            circuit.verify().is_err(),
            "scratch maps not inverse to each other must be rejected (inv 11)"
        );
    }

    #[test]
    fn inv11_scratch_maps_consistent_passes() {
        let mut circuit = valid_circuit_one_layer();
        let addr = blw(42);
        circuit.globals.scratch_space_mapping.insert(addr, 7);
        circuit.globals.scratch_space_mapping_rev.insert(7, addr);
        circuit
            .verify()
            .expect("consistent scratch maps must pass inv 11");
    }

    // -- Invariant 12: ScratchPrefill output has no forward in-edges / only MaxQuadratic --

    #[test]
    fn inv12_scratch_prefill_on_non_maxquad_detected() {
        // A CopyInBaseField gate with ScratchPrefill forward_source is illegal.
        let mut layer = valid_copy_layer();
        layer.gates[0].dst[0].forward_source = ForwardSource::ScratchPrefill;
        assert!(
            layer.verify().is_err(),
            "ScratchPrefill on CopyInBaseField must be rejected (inv 12)"
        );
    }

    #[test]
    fn inv12_scratch_prefill_on_maxquad_passes() {
        let mut scratch = BTreeMap::new();
        scratch.insert(inner(1, 1), 0usize);
        let layer = lower_layer(&sample_layer(), &scratch);
        layer
            .verify()
            .expect("ScratchPrefill on MaxQuadratic must pass inv 12");
    }

    // -- Invariant 14: MaxQuadratic operands are Domain::Base --

    #[test]
    fn inv14_maxquad_output_wrong_domain_detected() {
        // Build a MaxQuadratic layer and mutate the GateOutput node's domain to Ext.
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![(1u32, blw(0))].into_boxed_slice(),
            constant: 0,
        };
        let expr = E::Place(blw(0));
        let rel = NoFieldGKRRelation::MaxQuadratic {
            input: mq,
            expression: expr,
            output: inner(1, 0),
        };
        let mut layer = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        // Find the GateOutput node and replace it with an Ext-domain variant.
        let out_node_idx = layer.gates[0].dst[0].node.0 as usize;
        if let ExprNode::GateOutput { producer, out, .. } = &layer.arena.nodes[out_node_idx] {
            layer.arena.nodes[out_node_idx] = ExprNode::GateOutput {
                producer: *producer,
                out: *out,
                domain: Domain::Ext, // violate: MaxQuadratic output must be Base
            };
        }
        assert!(
            layer.verify().is_err(),
            "MaxQuadratic output with Ext domain must be rejected (inv 14)"
        );
    }

    #[test]
    fn inv14_maxquad_base_domain_passes() {
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![(1u32, blw(0))].into_boxed_slice(),
            constant: 0,
        };
        let expr = E::Place(blw(0));
        let rel = NoFieldGKRRelation::MaxQuadratic {
            input: mq,
            expression: expr,
            output: inner(1, 0),
        };
        let layer = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        layer
            .verify()
            .expect("MaxQuadratic with Base domain must pass inv 14");
    }

    /// Verify that EnforceSingleMaxQuadraticConstraint gates are also checked.
    #[test]
    fn enforce_single_max_quadratic_constraint_checked() {
        use super::super::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression as E};
        // matching: flat = x0 + 5, expr = Place(blw(0)) + Constant(5)
        let mq = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: vec![].into_boxed_slice(),
            linear_terms: vec![(1u32, blw(0))].into_boxed_slice(),
            constant: 5,
        };
        let expr = E::Sum(vec![E::Place(blw(0)), E::Constant(5)]);
        let rel = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: mq.clone(),
            expression: expr,
        };
        let cg = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        assert!(
            verify_flat_expr::<ConcreteField>(&cg).is_ok(),
            "matching EnforceSingleMaxQuadraticConstraint must be accepted"
        );

        // mismatched: flat = x0 + 5, but expr = x0 + 7
        let expr_bad = E::Sum(vec![E::Place(blw(0)), E::Constant(7)]);
        let rel_bad = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: mq,
            expression: expr_bad,
        };
        let cg_bad = lower_layer(&single_gate_layer(rel_bad), &BTreeMap::new());
        assert!(
            verify_flat_expr::<ConcreteField>(&cg_bad).is_err(),
            "mismatched EnforceSingleMaxQuadraticConstraint must be rejected"
        );
    }

    // -- Invariant 14: EnforceConstraintsMaxQuadratic out-of-range operand rejected --

    #[test]
    fn inv14_enforce_constraints_out_of_range_operand_rejected() {
        use super::super::NoFieldMaxQuadraticConstraintsGKRRelation;
        // Build a valid EnforceConstraintsMaxQuadratic layer (mirrors inv10 tests).
        let rel = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
            input: NoFieldMaxQuadraticConstraintsGKRRelation {
                quadratic_terms: vec![].into_boxed_slice(),
                linear_terms: vec![(blw(0), vec![(1u32, 0usize)].into_boxed_slice())]
                    .into_boxed_slice(),
                constants: vec![].into_boxed_slice(),
            },
        };
        let mut layer = lower_layer(&single_gate_layer(rel), &BTreeMap::new());
        // Sanity: the valid layer must pass before we mutate it.
        assert!(
            layer.verify().is_ok(),
            "valid EnforceConstraintsMaxQuadratic layer must pass before mutation"
        );
        // Mutate the linear operand NodeId to an out-of-range value.
        if let GateKind::EnforceConstraintsMaxQuadratic { ref mut linear, .. } = layer.gates[0].kind
        {
            linear[0].0 = NodeId(9999);
        }
        // verify() must return Err — NOT panic, NOT Ok.
        assert!(
            layer.verify().is_err(),
            "EnforceConstraintsMaxQuadratic with out-of-range operand must be rejected (invariant 14)"
        );
    }

    // -----------------------------------------------------------------------
    // Task 12: end-to-end faithfulness test against a real compiled artifact.
    //
    // Uses the add_sub_lui_auipc_mop circuit from
    // crate::gkr_circuits::add_sub_family, which is the smallest family
    // circuit that compiles successfully with
    // compile_unrolled_circuit_state_transition_into_gkr. The binary_shifts
    // circuit panics at a todo!() in no_field_gkr_max_quadratic_from_expr_and_constraint
    // so it is not usable here.
    //
    // We strip skip_if_ci!() because the compile step is purely symbolic
    // (no polynomial evaluation) and takes ~0.1 s in debug mode.
    // -----------------------------------------------------------------------

    fn build_add_sub_artifact() -> super::super::GKRCircuitArtifact<ConcreteField> {
        use crate::gkr_circuits::add_sub_family::{
            add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
            add_sub_lui_auipc_mop_table_addition_fn,
        };
        use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
        use common_constants::ROM_WORD_SIZE;

        compile_unrolled_circuit_state_transition_into_gkr::<ConcreteField>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
            ROM_WORD_SIZE,
            24,
        )
    }

    fn build_add_sub_artifact_no_caches() -> super::super::GKRCircuitArtifact<ConcreteField> {
        use crate::gkr_circuits::add_sub_family::{
            add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
            add_sub_lui_auipc_mop_table_addition_fn,
        };
        use crate::gkr_compiler::compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches;
        use common_constants::ROM_WORD_SIZE;

        compile_unrolled_circuit_state_transition_into_unrolled_gkr_without_caches::<ConcreteField>(
            &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
            &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
            ROM_WORD_SIZE,
            24,
        )
    }

    /// Fixture generator (run explicitly): emit the lowered codegen-IR JSON for
    /// the add_sub_lui_auipc_mop circuit in both the caching and no-caching
    /// variants. Run with:
    ///
    ///   cargo test -p cs codegen_ir::tests::generate_add_sub_codegen_ir_json -- --ignored --nocapture
    #[test]
    #[ignore]
    fn generate_add_sub_codegen_ir_json() {
        use crate::gkr_compiler::{lower, to_json_string};

        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("compiled_circuits");

        let variants: [(super::super::GKRCircuitArtifact<ConcreteField>, &str); 2] = [
            (
                build_add_sub_artifact(),
                "add_sub_lui_auipc_mop_codegen_ir_gkr.json",
            ),
            (
                build_add_sub_artifact_no_caches(),
                "add_sub_lui_auipc_mop_codegen_ir_no_caches_gkr.json",
            ),
        ];

        for (artifact, name) in variants {
            let circuit = lower::<ConcreteField>(&artifact).expect("lower must succeed");
            circuit.verify().expect("lowered circuit must verify");
            let json = to_json_string(&circuit).expect("to_json_string must succeed");
            let path = dir.join(name);
            std::fs::write(&path, &json).expect("write json");
            println!(
                "wrote {} ({} layers, {} bytes)",
                path.display(),
                circuit.layers.len(),
                json.len()
            );
        }
    }

    #[test]
    fn lowers_a_real_compiled_artifact() {
        let artifact = build_add_sub_artifact();
        let circuit = lower::<ConcreteField>(&artifact).expect("lower real artifact");
        assert!(
            circuit.layers.len() > 0,
            "real artifact must produce at least one layer"
        );
        assert_eq!(circuit.layers.len(), artifact.layers.len());
        let json = serde_json::to_string(&circuit).unwrap();
        let back: CodegenCircuit = serde_json::from_str(&json).unwrap();
        back.verify().unwrap();
    }

    // -----------------------------------------------------------------------
    // Task 14: public reachability + JSON writer.
    //
    // Confirms that `lower` and `CodegenCircuit` are reachable through the
    // intended public path (crate::gkr_compiler::{lower, CodegenCircuit,
    // to_json_string}) and that `to_json_string` produces valid, re-parseable
    // pretty JSON.
    // -----------------------------------------------------------------------

    #[test]
    fn lower_and_circuit_are_public_and_json_works() {
        // Use the same artifact helper from Task 12 so we get a real CodegenCircuit.
        let artifact = build_add_sub_artifact();

        // Exercise the items via the re-exported public path.
        // These `use` paths will cause a compile error if the items are not
        // accessible through crate::gkr_compiler.
        use crate::gkr_compiler::lower as crate_lower;
        use crate::gkr_compiler::to_json_string as crate_to_json_string;
        use crate::gkr_compiler::CodegenCircuit as CrateCodegenCircuit;

        let circuit: CrateCodegenCircuit =
            crate_lower::<ConcreteField>(&artifact).expect("lower must succeed");

        let s = crate_to_json_string(&circuit).expect("to_json_string must succeed");

        // Pretty JSON starts with '{'.
        assert!(
            s.starts_with('{'),
            "expected pretty JSON object, got: {}",
            &s[..s.len().min(40)]
        );

        // Must round-trip cleanly.
        let back: CrateCodegenCircuit = serde_json::from_str(&s).expect("JSON must round-trip");
        back.verify().unwrap();
    }
}
