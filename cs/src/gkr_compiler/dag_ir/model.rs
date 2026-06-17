use std::collections::BTreeMap;

// ── ID newtypes ──────────────────────────────────────────────────────────────

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord,
    serde::Serialize, serde::Deserialize,
)]
pub struct SourceId(pub u32);

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord,
    serde::Serialize, serde::Deserialize,
)]
pub struct ExprId(pub u32);

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord,
    serde::Serialize, serde::Deserialize,
)]
pub struct RootId(pub u32);

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord,
    serde::Serialize, serde::Deserialize,
)]
pub struct SinkId(pub u32);

// ── Field kind ───────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum FieldKind {
    Base,
    Ext,
}

// ── ReadPlace ────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ReadPlace {
    BaseLayerMemory { column: usize },
    BaseLayerWitness { column: usize },
    Setup { column: usize },
    Scratch { slot: usize },
    LayerOutput { layer: usize, offset: usize },
    CacheOutput { layer: usize, offset: usize },
}

// ── LookupValueKind ──────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum LookupValueKind {
    RangeCheck16Index,
    TimestampIndex,
    GenericColumn { column: usize },
    DecoderColumn { column: usize },
}

// ── VirtualSetupKind ─────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum VirtualSetupKind {
    RangeCheck16Bits,
    RangeCheckTimestamp,
    InitsAndTeardownsLow,
    InitsAndTeardownsHigh,
}

// ── ChallengePower ───────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ChallengePower {
    One,
    Static(u32),
}

// ── PermutationSlot ──────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum PermutationSlot {
    AddressLow,
    AddressHigh,
    TimestampLow,
    TimestampHigh,
    ValueLow,
    ValueHigh,
}

// ── ChallengeKey ─────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ChallengeKey {
    LookupAdditive,
    LookupMultiplicative,
    PermutationAdditive,
    PermutationLinearization(PermutationSlot),
    ConstraintAggregation,
}

// ── ChallengeRef ─────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ChallengeRef {
    pub key: ChallengeKey,
    pub power: ChallengePower,
}

// ── SourceKind ───────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SourceKind {
    Read { place: ReadPlace },
    Prior { id: RootId },
    Constant { value: u32 },
    Challenge { reference: ChallengeRef },
    VirtualSetup { kind: VirtualSetupKind },
    LookupValue { kind: LookupValueKind, set_index: usize, query: ExprId },
}

// ── SourceInfo ───────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SourceInfo {
    pub kind: SourceKind,
}

// ── Expr ─────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Expr {
    Source(SourceId),
    Add(Vec<ExprId>),
    Mul(Vec<ExprId>),
}

// ── SinkKind ─────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SinkKind {
    Inner { layer: usize, offset: usize },
    Cache { layer: usize, offset: usize },
    Export { slot: usize },
    Scratch { slot: usize },
}

// ── SinkInfo ─────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SinkInfo {
    pub kind: SinkKind,
    pub field: FieldKind,
}

// ── Root ─────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Root {
    Output { expr: ExprId, sink: SinkId },
    Constraint { expr: ExprId },
}

// ── BatchingOrder ────────────────────────────────────────────────────────────

/// Claim-bearing roots only; drives the sumcheck batching order.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BatchingOrder {
    pub roots: Vec<RootId>,
}

// ── RootGroup / RootSlot / RootOrigin ────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RootGroup {
    Gates,
    GatesExternal,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RootSlot {
    Output(usize),
    Constraint(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RootOrigin {
    pub group: RootGroup,
    pub relation_index: usize,
    pub slot: RootSlot,
}

// ── DagGlobals ───────────────────────────────────────────────────────────────

/// Minimal globals for Milestone 1. Grows when the backend milestone needs it.
/// Does NOT mirror `CodegenGlobals` (those layout types lack `Default`).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub struct DagGlobals {
    pub trace_len: usize,
    /// Scratch-space size overrides keyed by slot index.
    pub scratch: BTreeMap<usize, usize>,
}

// ── DagLayer ─────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DagLayer {
    pub sources: Vec<SourceInfo>,
    pub exprs: Vec<Expr>,
    pub roots: Vec<Root>,
    pub sinks: Vec<SinkInfo>,
    pub batching: BatchingOrder,
    /// Sparse: only claim-bearing + constraint roots are present; cache roots absent.
    pub origins: BTreeMap<RootId, RootOrigin>,
}

// ── DagCircuit ───────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DagCircuit {
    pub layers: Vec<DagLayer>,
    pub globals: DagGlobals,
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Serde round-trip: one-layer DagCircuit with a Constant source,
    /// an Add expr referencing it, one Output root, and empty origins.
    #[test]
    fn serde_roundtrip_one_layer() {
        // Source: Constant(42)
        let src_id = SourceId(0);
        let source = SourceInfo {
            kind: SourceKind::Constant { value: 42 },
        };

        // Expr 0: Source(src_id)
        let expr_src_id = ExprId(0);
        let expr_src = Expr::Source(src_id);

        // Expr 1: Add([expr_src_id])
        let expr_add_id = ExprId(1);
        let expr_add = Expr::Add(vec![expr_src_id]);

        // Sink
        let sink_id = SinkId(0);
        let sink = SinkInfo {
            kind: SinkKind::Export { slot: 0 },
            field: FieldKind::Base,
        };

        // Root: Output using expr_add
        let root_id = RootId(0);
        let root = Root::Output { expr: expr_add_id, sink: sink_id };

        let layer = DagLayer {
            sources: vec![source],
            exprs: vec![expr_src, expr_add],
            roots: vec![root],
            sinks: vec![sink],
            batching: BatchingOrder { roots: vec![root_id] },
            origins: BTreeMap::new(), // sparse — empty for this test
        };

        let circuit = DagCircuit {
            layers: vec![layer],
            globals: DagGlobals::default(),
        };

        // Serialize → deserialize → compare
        let json = serde_json::to_string(&circuit).expect("serialize");
        let back: DagCircuit = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(back, circuit);
        assert_eq!(back.layers.len(), 1);
    }
}
