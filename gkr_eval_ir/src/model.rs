use std::collections::{BTreeMap, BTreeSet};

// ── ID newtypes ──────────────────────────────────────────────────────────────

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct SourceId(pub u32);

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct ExprId(pub u32);

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct RootId(pub u32);

// ── Field kind ───────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum FieldKind {
    Base,
    Ext,
}

// ── ReadPlace ────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ReadPlace {
    BaseLayerMemory { column: usize },
    BaseLayerWitness { column: usize },
    Setup { column: usize },
    Scratch { slot: usize },
    LayerOutput { layer: usize, offset: usize },
    CacheOutput { layer: usize, offset: usize },
}

// ── LookupValueKind ──────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum LookupValueKind {
    RangeCheck16Index,
    TimestampIndex,
    GenericColumn { column: usize },
}

// ── VirtualSetupKind ─────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum VirtualSetupKind {
    RangeCheck16Bits,
    RangeCheckTimestamp,
    InitsAndTeardownsLow,
    InitsAndTeardownsHigh,
}

// ── ChallengePower ───────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ChallengePower {
    One,
    Static(u32),
}

// ── PermutationSlot ──────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum PermutationSlot {
    AddressLow,
    AddressHigh,
    TimestampLow,
    TimestampHigh,
    ValueLow,
    ValueHigh,
}

// ── ChallengeKey ─────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ChallengeKey {
    LookupAdditive,
    LookupMultiplicative,
    PermutationAdditive,
    PermutationLinearization(PermutationSlot),
    /// Powers of the per-layer claim-batching challenge beta, used by the backward
    /// alpha spine (`root_0 + Σ beta^i·root_i`). `ChallengePower::One` = beta¹,
    /// `Static(i)` = betaⁱ (i ≥ 2). Root 0 in batching order is UNSCALED (no
    /// challenge leaf at all); claim-only constraint roots still consume a power
    /// slot.
    ClaimBatching,
}

// ── ChallengeRef ─────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ChallengeRef {
    pub key: ChallengeKey,
    pub power: ChallengePower,
}

// ── SourceKind ───────────────────────────────────────────────────────────────

/// One runtime-selected init/teardown address prefix. The circuit fixes the
/// local set index and bit position; the proof input supplies the set's value.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct InitsAndTeardownsTopBitsRef {
    pub set_index: usize,
    pub shift: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SourceKind {
    Read {
        place: ReadPlace,
    },
    Constant {
        value: u32,
    },
    Challenge {
        reference: ChallengeRef,
    },
    VirtualSetup {
        kind: VirtualSetupKind,
    },
    InitsAndTeardownsTopBits {
        reference: InitsAndTeardownsTopBitsRef,
    },
    LookupValue {
        kind: LookupValueKind,
        set_index: usize,
        query: ExprId,
    },
}

// ── Expr ─────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Expr {
    Source(SourceId),
    Add(Vec<ExprId>),
    Mul(Vec<ExprId>),
}

// ── SinkKind ─────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SinkKind {
    Inner { layer: usize, offset: usize },
    Cache { layer: usize, offset: usize },
    Scratch { slot: usize },
}

impl SinkKind {
    pub fn read_place(&self) -> Option<ReadPlace> {
        match *self {
            Self::Inner { layer, offset } => Some(ReadPlace::LayerOutput { layer, offset }),
            Self::Cache { layer, offset } => Some(ReadPlace::CacheOutput { layer, offset }),
            Self::Scratch { .. } => None,
        }
    }
}

// ── SinkInfo ─────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SinkInfo {
    pub kind: SinkKind,
    pub field: FieldKind,
}

// ── Root ─────────────────────────────────────────────────────────────────────

/// A value observed outside pure forward dataflow. Materialization and claims
/// are independent; a root carries either or both.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Root {
    pub expr: ExprId,
    /// Where this value is materialized, if anywhere.
    pub materialize: Option<SinkInfo>,
    /// Claim-bearing batching identity; `None` = not claim-bearing.
    pub claim: Option<RootOrigin>,
}

// ── BatchingOrder ────────────────────────────────────────────────────────────

/// Claim-bearing roots only; drives the sumcheck batching order.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BatchingOrder {
    pub roots: Vec<RootId>,
}

// ── RootOrigin ───────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RootGroup {
    Gates,
    GatesExternal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RootOrigin {
    pub group: RootGroup,
    pub relation_index: usize,
}

// ── ResolutionStrategy ───────────────────────────────────────────────────────

/// How the forward codegen MAY materialize a lookup/setup fold-leaf as a fast
/// "peek" of a precomputed array, instead of re-evaluating the authoritative
/// `expr`. Sparse: absent from `DagLayer::resolutions` ⇒ recompute (walk the
/// expr). Forward-only — the backward (sumcheck) pass never consumes it. The
/// `expr` stays authoritative; this is guidance, not a redefinition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ResolutionStrategy {
    /// Range or timestamp value from one mapping column.
    PeekSingleColumn { set_index: usize, width: RangeWidth },
    /// Generic lookup-table value selected by a mapping column.
    PeekAggregate { set_index: usize },
    /// Row-indexed setup value, zero-padded past the table length.
    PeekSetup,
    /// Decoder lookup value selected by its predicate.
    PeekDecoder { predicate: ReadPlace },
}

/// Selects the single-column mapping array (and the stored element width).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum RangeWidth {
    /// `range_check_16_lookup_mapping` (16-bit).
    Bits16,
    /// `timestamp_range_check_lookup_mapping`.
    Timestamp,
}

// ── DagLayer ─────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DagLayer {
    pub sources: Vec<SourceKind>,
    pub exprs: Vec<Expr>,
    pub roots: Vec<Root>,
    pub batching: BatchingOrder,
    /// Sparse forward-peek hints keyed by lookup/setup fold-leaf `ExprId`.
    /// Missing entries are recomputed from the expression.
    pub resolutions: BTreeMap<ExprId, ResolutionStrategy>,
    pub forward_skip_roots: BTreeSet<RootId>,
}

// ── DagCircuit ───────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DagCircuit {
    pub layers: Vec<DagLayer>,
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Serde round-trip: one-layer DagCircuit with a Constant source,
    /// an Add expr referencing it, and one claim-bearing Output root (its sink
    /// inlined into `materialize`, its origin into `claim`).
    #[test]
    fn serde_roundtrip_one_layer() {
        // Source: Constant(42)
        let src_id = SourceId(0);
        let source = SourceKind::Constant { value: 42 };

        // Expr 0: Source(src_id)
        let expr_src_id = ExprId(0);
        let expr_src = Expr::Source(src_id);

        // Expr 1: Add([expr_src_id])
        let expr_add_id = ExprId(1);
        let expr_add = Expr::Add(vec![expr_src_id]);

        // Root: claim-bearing Output using expr_add; sink + origin inlined.
        let root_id = RootId(0);
        let root = Root {
            expr: expr_add_id,
            materialize: Some(SinkInfo {
                kind: SinkKind::Inner {
                    layer: 0,
                    offset: 0,
                },
                field: FieldKind::Base,
            }),
            claim: Some(RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
            }),
        };

        let layer = DagLayer {
            sources: vec![source],
            exprs: vec![expr_src, expr_add],
            roots: vec![root],
            batching: BatchingOrder {
                roots: vec![root_id],
            },
            resolutions: BTreeMap::new(),
            forward_skip_roots: BTreeSet::new(),
        };

        let circuit = DagCircuit {
            layers: vec![layer],
        };

        // Serialize → deserialize → compare
        let json = serde_json::to_string(&circuit).expect("serialize");
        let back: DagCircuit = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(back, circuit);
        assert_eq!(back.layers.len(), 1);
    }
}
