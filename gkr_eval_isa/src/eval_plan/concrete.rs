use std::collections::{BTreeMap, HashMap, HashSet};

use gkr_eval_ir::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, RootId, SinkInfo, SinkKind, SourceKind,
};

use crate::bwd::batch::{
    BATCH_COEFFICIENT_MAX, BATCH_COEFFICIENT_ONE, pack_batch_dst, unpack_batch_dst,
};
use crate::bwd::source::{BwdSpecial, BwdSpecialTable, OriginLeaf};
use crate::fwd::binding::{BackingKey, SourceMarkerMode, bind_final_sources};
use crate::fwd::compile::{copy_src_read_place, read_place_operand_field};
use crate::fwd::context::{
    CompileTrace, CompiledLayer, DagForwardContext, ForwardAction, OutputCell, RootOutput,
};
use crate::fwd::encode::{decode, encode, encoded_lane_count};
use crate::fwd::error::{BindError, DecodeError, EncodeError};
use crate::fwd::isa::{
    DstLine, Instr, LdcSub, MAX_CELL, MAX_DESC, MovDir, OperandField, OperandLine, Program, Sign,
    Special,
};
use crate::fwd::source::{SpecialDescriptor, SpecialStrategy, lower_resolution};
use crate::fwd::stats::{CompileStats, OP_ADD, OP_FMA, OP_MOV, OP_MUL};
use crate::fwd::{disasm::disassemble_layer, error::CompileError, validate::validate_compiled};

use super::{
    CacheStoreFrom, IdentityError, MaterializeFrom, Operand, PackedEvalOp, PackedEvalPlan, RootKey,
    TempId, ValueFingerprint, ValueRef, field_lanes, structural_fingerprints, unit_sign_expr,
};

const BABYBEAR_NEG_ONE: u32 = 0x7800_0001 - 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConcreteBindError {
    BudgetOutOfRange(usize),
    Bind(BindError),
    Encode(EncodeError),
    Decode(DecodeError),
    Identity(IdentityError),
    DuplicateResident(ValueFingerprint),
    MissingResident(ValueFingerprint),
    MissingDroppedResident(ValueFingerprint),
    DuplicateTemp(TempId),
    MissingTemp(TempId),
    MissingStorageLocation(u32),
    RelocationSourceMismatch {
        id: u32,
        expected: u16,
        actual: u16,
    },
    UnsupportedCopyAliasSource(RootId),
    UnencodableZero(ExprId),
    MultiplicationByOne(ExprId),
    MultiplicationByNegOne(ExprId),
    MultiplicationBySyntheticUnit {
        negative: bool,
    },
    LiveTempsAtEnd(Vec<TempId>),
    PlacementFailed {
        budget_lanes: usize,
        peak_live_lanes: usize,
        telemetry: PlacementTelemetry,
    },
    MissingDefinition(usize),
    UncoveredLookup(ValueRef),
    ExpectedSource(ValueRef),
    DescriptorOverflow,
    RootCountMismatch {
        expected: usize,
        actual: usize,
    },
    RootIdentityMismatch {
        root: RootId,
    },
    DuplicateReturnAcc,
    DuplicateReturnBatch,
    MixedForwardAndReturnTerminal,
    Validation(CompileError),
    InstructionCountMismatch {
        predicted: usize,
        emitted: usize,
    },
    EncodedLaneMismatch {
        predicted: usize,
        emitted: usize,
    },
    DramTrafficMismatch {
        predicted: usize,
        emitted: usize,
    },
    EncodeRoundtripMismatch,
    BackwardSpecialRequiresBindings {
        desc: u16,
    },
    BatchAccumulateRequiresBackwardMode,
    ReturnBatchRequiresBackwardMode,
    InvalidBatchCoefficientDescriptor {
        desc: u16,
    },
    MissingReturnBatch,
    SinkFreeBatch,
    UnboundBackwardSource(ExprId),
    BackwardCommit,
}

impl From<BindError> for ConcreteBindError {
    fn from(value: BindError) -> Self {
        Self::Bind(value)
    }
}

impl From<EncodeError> for ConcreteBindError {
    fn from(value: EncodeError) -> Self {
        Self::Encode(value)
    }
}

impl From<DecodeError> for ConcreteBindError {
    fn from(value: DecodeError) -> Self {
        Self::Decode(value)
    }
}

impl From<IdentityError> for ConcreteBindError {
    fn from(value: IdentityError) -> Self {
        Self::Identity(value)
    }
}

impl From<CompileError> for ConcreteBindError {
    fn from(value: CompileError) -> Self {
        Self::Validation(value)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConcreteBindingStats {
    pub encoded_lanes: usize,
    pub max_live_lanes: usize,
    pub relocation_moves: usize,
    pub placement: PlacementTelemetry,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PlacementTelemetry {
    pub exact_attempted: bool,
    pub relocation_fallback: bool,
    pub ext_nodes: u64,
    pub base_nodes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StorageMove {
    id: StorageId,
    from: u16,
    to: u16,
}

struct PhysicalPlacement {
    definition_locations: HashMap<StorageId, u16>,
    moves_at: HashMap<usize, Vec<StorageMove>>,
}

impl PhysicalPlacement {
    fn fixed(definition_locations: HashMap<StorageId, u16>) -> Self {
        Self {
            definition_locations,
            moves_at: HashMap::new(),
        }
    }

    fn move_count(&self) -> usize {
        self.moves_at.values().map(Vec::len).sum()
    }
}

pub struct ConcreteEvalProgram {
    pub compiled: CompiledLayer,
    pub encoded: Vec<u16>,
    pub stats: ConcreteBindingStats,
    pub terminal: ConcreteTerminal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConcreteTerminal {
    Forward,
    ReturnAcc { root: RootKey },
    ReturnBatch { root: RootKey },
}

/// Independently validate the forward instruction stream and its concrete
/// terminal contract.
pub fn validate_concrete_eval_program(
    concrete: &ConcreteEvalProgram,
    layer: &DagLayer,
) -> Result<(), ConcreteBindError> {
    validate_compiled(&concrete.compiled, layer)?;
    match &concrete.terminal {
        ConcreteTerminal::Forward => {
            let expected = concrete.compiled.ctx.actions.len();
            let actual = concrete.compiled.root_outputs.len() + concrete.compiled.skipped.len();
            let mut classified = HashSet::with_capacity(actual);
            let outputs_match_actions =
                concrete.compiled.root_outputs.iter().all(|(root, output)| {
                    classified.insert(*root)
                        && matches!(
                            (concrete.compiled.ctx.actions.get(root), output),
                            (Some(ForwardAction::Compute), RootOutput::Cell(_))
                                | (Some(ForwardAction::CopyAlias { .. }), RootOutput::Alias(_))
                        )
                });
            let skipped_match_actions = concrete.compiled.skipped.iter().all(|root| {
                classified.insert(*root)
                    && matches!(
                        concrete.compiled.ctx.actions.get(root),
                        Some(ForwardAction::SkipScratchPrefill)
                    )
            });
            if actual != expected
                || classified.len() != expected
                || !outputs_match_actions
                || !skipped_match_actions
            {
                return Err(ConcreteBindError::RootCountMismatch { expected, actual });
            }
        }
        ConcreteTerminal::ReturnAcc { root } | ConcreteTerminal::ReturnBatch { root } => {
            if !concrete.compiled.ctx.actions.is_empty()
                || !concrete.compiled.ctx.cache_loc.is_empty()
                || !concrete.compiled.root_outputs.is_empty()
                || !concrete.compiled.skipped.is_empty()
            {
                return Err(ConcreteBindError::MixedForwardAndReturnTerminal);
            }
            let fingerprints = structural_fingerprints(layer)?;
            let matches = layer
                .roots
                .iter()
                .enumerate()
                .filter(|(index, candidate)| {
                    candidate.materialize.is_none()
                        && root_key(layer, &fingerprints, RootId(*index as u32)) == *root
                })
                .count();
            if matches != 1 {
                return Err(ConcreteBindError::RootCountMismatch {
                    expected: 1,
                    actual: matches,
                });
            }
        }
    }
    Ok(())
}

/// Disassemble a concrete evaluation program and its non-ISA terminal.
pub fn disassemble_concrete_eval_program(
    title: &str,
    concrete: &ConcreteEvalProgram,
    layer: Option<&DagLayer>,
) -> String {
    let mut disassembly = disassemble_layer(title, &concrete.compiled, layer);
    disassembly.push_str(match concrete.terminal {
        ConcreteTerminal::Forward => "terminal = Forward\n",
        ConcreteTerminal::ReturnAcc { .. } => "terminal = ReturnAcc\n",
        ConcreteTerminal::ReturnBatch { .. } => "terminal = ReturnBatch\n",
    });
    disassembly
}

/// Bind symbolic sources, residents, temporaries, and sinks to the existing
/// forward VM's concrete operand namespaces and emit an encodable `Program`.
pub fn bind_packed_plan(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root_order: &[RootId],
    this_layer: usize,
    budget_lanes: usize,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    // Keep relocation exceptional: exhaust the fixed-location two-pass
    // allocator (E4 quads first, BF lanes second) before allowing any move.
    bind_packed_plan_with_mode(
        packed,
        layer,
        root_order,
        this_layer,
        budget_lanes,
        PlacementMode::Exact,
    )
}

/// Bind a plan and attach the non-ISA forward actions classified from the
/// artifact layer. `CopyAlias` roots become stable-backing `RootOutput::Alias`
/// entries. Scratch-prefill roots, whose values were already created during
/// witness generation, populate `CompiledLayer::skipped`. Neither action adds
/// instructions, loads/stores, or DRAM traffic.
pub fn bind_packed_plan_with_actions(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root_order: &[RootId],
    this_layer: usize,
    budget_lanes: usize,
    actions: &HashMap<RootId, ForwardAction>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    let mut concrete = bind_packed_plan(packed, layer, root_order, this_layer, budget_lanes)?;
    if !actions.is_empty() && !matches!(concrete.terminal, ConcreteTerminal::Forward) {
        return Err(ConcreteBindError::MixedForwardAndReturnTerminal);
    }
    concrete.compiled.ctx.actions = actions.clone();
    concrete.compiled.ctx.cross_layer_fields = cross_layer_fields.clone();

    let mut ordered_actions = actions.iter().collect::<Vec<_>>();
    ordered_actions.sort_by_key(|entry| entry.0.0);
    for (&root, action) in ordered_actions {
        match action {
            ForwardAction::Compute => {}
            ForwardAction::CopyAlias { src_addr, .. } => {
                let place = copy_src_read_place(*src_addr)
                    .ok_or(ConcreteBindError::UnsupportedCopyAliasSource(root))?;
                let fallback = layer.roots[root.0 as usize]
                    .materialize
                    .as_ref()
                    .map_or(OperandField::Base, |sink| to_operand_field(sink.field));
                let field = read_place_operand_field(&place, cross_layer_fields, fallback);
                let (slot, col) = concrete
                    .compiled
                    .ctx
                    .backings
                    .read_slot_col(&place, field)?;
                concrete.compiled.root_outputs.push((
                    root,
                    RootOutput::Alias(OperandLine::LogicalGlobal { slot, col }),
                ));
            }
            ForwardAction::SkipScratchPrefill => concrete.compiled.skipped.push(root),
        }
    }
    Ok(concrete)
}

pub(super) fn bind_packed_plan_greedy(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root_order: &[RootId],
    this_layer: usize,
    budget_lanes: usize,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    bind_packed_plan_with_mode(
        packed,
        layer,
        root_order,
        this_layer,
        budget_lanes,
        PlacementMode::GreedyOnly,
    )
}

/// Fast concrete certificate for intermediate search candidates. This keeps
/// greedy fixed placement first, but defers bounded exact fixed placement to
/// the final winner certification instead of repeating it for every incumbent.
pub(super) fn bind_packed_plan_for_search(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root_order: &[RootId],
    this_layer: usize,
    budget_lanes: usize,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    bind_packed_plan_with_mode(
        packed,
        layer,
        root_order,
        this_layer,
        budget_lanes,
        PlacementMode::Relocating,
    )
}

#[derive(Clone, Copy)]
enum PlacementMode {
    GreedyOnly,
    Relocating,
    Exact,
}

#[derive(Clone, Copy)]
enum ConcreteSourceMode<'a> {
    Forward,
    Backward {
        leaf_descs: &'a BTreeMap<ExprId, u16>,
        specials: &'a BwdSpecialTable,
        optimize_reads: bool,
    },
}

fn bind_packed_plan_with_mode(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root_order: &[RootId],
    this_layer: usize,
    budget_lanes: usize,
    placement_mode: PlacementMode,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    bind_packed_plan_with_source_mode(
        packed,
        layer,
        root_order,
        this_layer,
        budget_lanes,
        placement_mode,
        ConcreteSourceMode::Forward,
    )
}

pub(super) fn bind_backward_packed_plan(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root: RootId,
    budget_lanes: usize,
    leaf_descs: &BTreeMap<ExprId, u16>,
    specials: &BwdSpecialTable,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    bind_backward_packed_plan_with_read_optimization(
        packed,
        layer,
        root,
        budget_lanes,
        leaf_descs,
        specials,
        true,
    )
}

pub(super) fn bind_backward_packed_plan_for_model(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root: RootId,
    budget_lanes: usize,
    leaf_descs: &BTreeMap<ExprId, u16>,
    specials: &BwdSpecialTable,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    bind_backward_packed_plan_with_read_optimization(
        packed,
        layer,
        root,
        budget_lanes,
        leaf_descs,
        specials,
        false,
    )
}

fn bind_backward_packed_plan_with_read_optimization(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root: RootId,
    budget_lanes: usize,
    leaf_descs: &BTreeMap<ExprId, u16>,
    specials: &BwdSpecialTable,
    optimize_reads: bool,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    bind_packed_plan_with_source_mode(
        packed,
        layer,
        &[root],
        0,
        budget_lanes,
        PlacementMode::Exact,
        ConcreteSourceMode::Backward {
            leaf_descs,
            specials,
            optimize_reads,
        },
    )
}

fn bind_packed_plan_with_source_mode(
    packed: &PackedEvalPlan,
    layer: &DagLayer,
    root_order: &[RootId],
    this_layer: usize,
    budget_lanes: usize,
    placement_mode: PlacementMode,
    source_mode: ConcreteSourceMode<'_>,
) -> Result<ConcreteEvalProgram, ConcreteBindError> {
    if budget_lanes == 0 || budget_lanes > MAX_CELL as usize {
        return Err(ConcreteBindError::BudgetOutOfRange(budget_lanes));
    }
    let lifetimes = analyze_lifetimes(packed, source_mode)?;
    let peak_live_lanes = peak_live_lanes(&lifetimes.intervals);
    let fixed_mode = if matches!(placement_mode, PlacementMode::Exact) {
        PlacementMode::Exact
    } else {
        PlacementMode::GreedyOnly
    };
    let (physical, placement) =
        match place_intervals(&lifetimes.intervals, budget_lanes, fixed_mode) {
            Ok((locations, telemetry)) => (PhysicalPlacement::fixed(locations), telemetry),
            Err(mut telemetry) => {
                if matches!(placement_mode, PlacementMode::GreedyOnly) {
                    return Err(ConcreteBindError::PlacementFailed {
                        budget_lanes,
                        peak_live_lanes,
                        telemetry,
                    });
                }
                let physical = place_intervals_with_relocation(&lifetimes.intervals, budget_lanes)
                    .ok_or(ConcreteBindError::PlacementFailed {
                        budget_lanes,
                        peak_live_lanes,
                        telemetry,
                    })?;
                telemetry.relocation_fallback = true;
                (physical, telemetry)
            }
        };
    let relocation_moves = physical.move_count();
    let fingerprints = structural_fingerprints(layer)?;
    let pending_roots = root_order.iter().copied().collect::<HashSet<_>>();
    if pending_roots.len() != root_order.len() {
        return Err(ConcreteBindError::RootCountMismatch {
            expected: root_order.len(),
            actual: pending_roots.len(),
        });
    }
    let mut emitter = Emitter {
        layer,
        this_layer,
        fingerprints,
        lifetimes: &lifetimes,
        definition_locations: &physical.definition_locations,
        moves_at: &physical.moves_at,
        current_locations: HashMap::new(),
        ctx: DagForwardContext::default(),
        instrs: Vec::with_capacity(packed.stats.packed_instructions + relocation_moves),
        residents: HashMap::new(),
        temps: HashMap::new(),
        pending_roots,
        root_outputs: Vec::new(),
        terminal: None,
        batch_sinks: 0,
        desc_by_expr: HashMap::new(),
        source_mode,
    };
    for (index, op) in packed.ops.iter().enumerate() {
        emitter.emit(index, op)?;
    }
    if !emitter.temps.is_empty() {
        let mut live: Vec<_> = emitter.temps.keys().copied().collect();
        live.sort_by_key(|temp| temp.0);
        return Err(ConcreteBindError::LiveTempsAtEnd(live));
    }
    let terminal = match emitter.terminal.take() {
        Some(pending_terminal) => {
            let root = pending_terminal.root();
            if !emitter.root_outputs.is_empty()
                || emitter
                    .pending_roots
                    .iter()
                    .any(|root_id| layer.roots[root_id.0 as usize].materialize.is_some())
            {
                return Err(ConcreteBindError::MixedForwardAndReturnTerminal);
            }
            if emitter.pending_roots.len() != 1 {
                return Err(ConcreteBindError::RootCountMismatch {
                    expected: root_order.len(),
                    actual: root_order.len() - emitter.pending_roots.len(),
                });
            }
            let root_id = *emitter
                .pending_roots
                .iter()
                .next()
                .expect("one pending root was checked above");
            if root_key(layer, &emitter.fingerprints, root_id) != *root {
                return Err(ConcreteBindError::RootIdentityMismatch { root: root_id });
            }
            match pending_terminal {
                PendingTerminal::ReturnAcc(root) => {
                    if matches!(source_mode, ConcreteSourceMode::Backward { .. }) {
                        return Err(ConcreteBindError::MissingReturnBatch);
                    }
                    ConcreteTerminal::ReturnAcc { root }
                }
                PendingTerminal::ReturnBatch(root) => {
                    if emitter.batch_sinks == 0 {
                        return Err(ConcreteBindError::SinkFreeBatch);
                    }
                    ConcreteTerminal::ReturnBatch { root }
                }
            }
        }
        None => {
            if matches!(source_mode, ConcreteSourceMode::Backward { .. }) {
                return Err(ConcreteBindError::MissingReturnBatch);
            }
            if !emitter.pending_roots.is_empty() {
                return Err(ConcreteBindError::RootCountMismatch {
                    expected: root_order.len(),
                    actual: root_order.len() - emitter.pending_roots.len(),
                });
            }
            ConcreteTerminal::Forward
        }
    };

    let emitted_program = Program {
        instrs: emitter.instrs,
    };
    let expected_instructions = packed.stats.packed_instructions + relocation_moves;
    if emitted_program.instrs.len() != expected_instructions {
        return Err(ConcreteBindError::InstructionCountMismatch {
            predicted: expected_instructions,
            emitted: emitted_program.instrs.len(),
        });
    }
    let emitted_encoded_lanes = encoded_lane_count(&emitted_program)?;
    let expected_encoded_lanes = packed.stats.encoded_lanes + 3 * relocation_moves;
    if emitted_encoded_lanes != expected_encoded_lanes {
        return Err(ConcreteBindError::EncodedLaneMismatch {
            predicted: expected_encoded_lanes,
            emitted: emitted_encoded_lanes,
        });
    }

    let mut program = emitted_program;
    let backward_config = match source_mode {
        ConcreteSourceMode::Forward => None,
        ConcreteSourceMode::Backward {
            specials,
            optimize_reads,
            ..
        } => Some((specials, optimize_reads)),
    };
    let backward_mode = backward_config.is_some();
    fold_direct_source_stores_with_mode(&mut program, backward_mode);
    fold_load_mul_add(&mut program);
    elide_accumulator_cell_roundtrips(&mut program);
    if let Some((specials, optimize_reads)) = backward_config {
        if optimize_reads {
            hoist_raw_source_batch_sinks(&mut program);
            elide_reloads_of_acc_preserved_by_batch_sink(&mut program, specials);
        }
    }
    let marker_mode = match source_mode {
        ConcreteSourceMode::Forward => SourceMarkerMode::Forward,
        ConcreteSourceMode::Backward { .. } => SourceMarkerMode::Backward,
    };
    emitter.ctx.source_windows =
        bind_final_sources(&mut program, &emitter.ctx.backings, marker_mode)?;
    let encoded = encode(&program)?;
    let encoded_lanes = encoded.len();
    if decode(&encoded)? != program {
        return Err(ConcreteBindError::EncodeRoundtripMismatch);
    }
    let compile_stats = tally_program(&program, &emitter.ctx, peak_live_lanes);
    if matches!(source_mode, ConcreteSourceMode::Forward)
        && compile_stats.dram_traffic != packed.stats.dram_read_lanes
    {
        return Err(ConcreteBindError::DramTrafficMismatch {
            predicted: packed.stats.dram_read_lanes,
            emitted: compile_stats.dram_traffic,
        });
    }
    let trace = CompileTrace {
        max_live_cells: peak_live_lanes,
        ..CompileTrace::default()
    };
    let compiled = CompiledLayer {
        program,
        ctx: emitter.ctx,
        root_outputs: emitter.root_outputs,
        skipped: Vec::new(),
        trace,
        budget: budget_lanes,
        stats: compile_stats,
        resident_realized: Vec::new(),
    };
    Ok(ConcreteEvalProgram {
        compiled,
        encoded,
        stats: ConcreteBindingStats {
            encoded_lanes,
            max_live_lanes: peak_live_lanes,
            relocation_moves,
            placement,
        },
        terminal,
    })
}

/// Replace `acc <- source; dst <- acc; acc <- other` with a direct
/// `dst <- source` move. The final load proves that the accumulator value from
/// the first load is dead after the store.
fn fold_direct_source_stores(program: &mut Program) {
    fold_direct_source_stores_with_mode(program, false);
}

fn fold_direct_source_stores_with_mode(program: &mut Program, preserve_batch_sinks: bool) {
    let original = std::mem::take(&mut program.instrs);
    let mut rewritten = Vec::with_capacity(original.len());
    let mut index = 0;
    while index < original.len() {
        let replacement = original.get(index..index + 3).and_then(|window| {
            let (
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: load_field,
                    dst: None,
                    src: Some(source),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: store_field,
                    dst: Some(destination),
                    src: None,
                },
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    dst: None,
                    src: Some(_),
                    ..
                },
            ) = (&window[0], &window[1], &window[2])
            else {
                return None;
            };
            if preserve_batch_sinks && unpack_batch_dst(destination).is_some() {
                return None;
            }
            (load_field == store_field).then_some(Instr::Mov {
                dir: MovDir::DstFromSrc,
                field: *load_field,
                dst: Some(*destination),
                src: Some(*source),
            })
        });
        if let Some(instruction) = replacement {
            rewritten.push(instruction);
            index += 2;
        } else {
            rewritten.push(original[index].clone());
            index += 1;
        }
    }
    program.instrs = rewritten;
}

/// Strength-reduce `acc <- A; acc *= X; acc += Y` to
/// `acc <- Y; acc += A*X`. Restrict the match to one positive Add operand and
/// one Mul operand; multiplication's accumulator-negate flag becomes the FMA
/// product sign.
fn fold_load_mul_add(program: &mut Program) {
    let original = std::mem::take(&mut program.instrs);
    let mut rewritten = Vec::with_capacity(original.len());
    let mut index = 0;
    while index < original.len() {
        let replacement = original.get(index..index + 3).and_then(|window| {
            let (
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: loaded_field,
                    dst: None,
                    src: Some(loaded),
                },
                Instr::Mul {
                    field: multiplied_field,
                    negate_acc,
                    operands: factors,
                    ..
                },
                Instr::Add {
                    field: added_field,
                    sign: Sign::Plus,
                    operands: addends,
                    ..
                },
            ) = (&window[0], &window[1], &window[2])
            else {
                return None;
            };
            let ([factor], [addend]) = (factors.as_slice(), addends.as_slice()) else {
                return None;
            };
            let (field_lhs, lhs, field_rhs, rhs) =
                if *loaded_field == OperandField::Ext && *multiplied_field == OperandField::Base {
                    (*multiplied_field, *factor, *loaded_field, *loaded)
                } else {
                    (*loaded_field, *loaded, *multiplied_field, *factor)
                };
            let product_is_ext =
                *loaded_field == OperandField::Ext || *multiplied_field == OperandField::Ext;
            Some((
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: *added_field,
                    dst: None,
                    src: Some(*addend),
                },
                Instr::Fma {
                    field_lhs,
                    field_rhs,
                    sign: if *negate_acc { Sign::Minus } else { Sign::Plus },
                    promote: *added_field == OperandField::Base && product_is_ext,
                    pairs: vec![(lhs, rhs)],
                },
            ))
        });
        if let Some((init, fma)) = replacement {
            rewritten.push(init);
            rewritten.push(fma);
            index += 3;
        } else {
            rewritten.push(original[index].clone());
            index += 1;
        }
    }
    program.instrs = rewritten;
}

/// Remove `cell <- acc; acc <- cell` round trips exposed only after logical
/// storage has been assigned to physical cells. The store leaves `acc`
/// unchanged, so the immediately following reload cannot affect VM state.
fn elide_accumulator_cell_roundtrips(program: &mut Program) {
    let mut rewritten = Vec::with_capacity(program.instrs.len());
    for instruction in program.instrs.drain(..) {
        let redundant = matches!(
            (rewritten.last(), &instruction),
            (
                Some(Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: stored_field,
                    dst: Some(DstLine::Smem { cell: stored_cell }),
                    src: None,
                }),
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: loaded_field,
                    dst: None,
                    src: Some(OperandLine::Smem { cell: loaded_cell }),
                },
            ) if stored_field == loaded_field && stored_cell == loaded_cell
        );
        if !redundant {
            rewritten.push(instruction);
        }
    }

    let mut without_dead_stores = Vec::with_capacity(rewritten.len());
    let mut index = 0;
    while index < rewritten.len() {
        let dead_store = rewritten.get(index..index + 3).is_some_and(|window| {
            let (
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: first_field,
                    dst: Some(DstLine::Smem { cell: first_cell }),
                    src: None,
                },
                Instr::Fma {
                    field_lhs,
                    field_rhs,
                    pairs,
                    ..
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: last_field,
                    dst: Some(DstLine::Smem { cell: last_cell }),
                    src: None,
                },
            ) = (&window[0], &window[1], &window[2])
            else {
                return false;
            };
            first_field == last_field
                && first_cell == last_cell
                && !pairs.iter().any(|(lhs, rhs)| {
                    smem_operand_overlaps(*lhs, *field_lhs, *first_cell, *first_field)
                        || smem_operand_overlaps(*rhs, *field_rhs, *first_cell, *first_field)
                })
        });
        if dead_store {
            without_dead_stores.push(rewritten[index + 1].clone());
            without_dead_stores.push(rewritten[index + 2].clone());
            index += 3;
        } else {
            without_dead_stores.push(rewritten[index].clone());
            index += 1;
        }
    }
    program.instrs = without_dead_stores;
}

/// `BatchAccumulate` updates the separate batch accumulator and leaves the VM
/// accumulator untouched. Remove an immediately following reload when the
/// instruction before the sink proves that the same value remains in `acc`.
fn elide_reloads_of_acc_preserved_by_batch_sink(program: &mut Program, specials: &BwdSpecialTable) {
    let mut delete = vec![false; program.instrs.len()];
    for (instruction, window) in program.instrs.windows(3).enumerate() {
        let sink = matches!(
            &window[1],
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                dst: Some(dst),
                src: None,
                ..
            } if unpack_batch_dst(dst).is_some()
        );
        let reloads_same_source = matches!(
            (&window[0], &window[2]),
            (
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: before_field,
                    src: Some(before_src),
                    ..
                },
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: after_field,
                    src: Some(after_src),
                    ..
                },
            ) if before_field == after_field
                && before_src == after_src
                && match before_src {
                    OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. } => true,
                    OperandLine::Smem { .. } | OperandLine::Ldc { .. } => true,
                    OperandLine::Special { desc } => {
                        matches!(specials.get(*desc), Some(BwdSpecial::VirtualSetup { .. }))
                    }
                    OperandLine::Source { .. } => false,
                }
        );
        let reloads_just_stored_acc = matches!(
            (&window[0], &window[2]),
            (
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: before_field,
                    dst: Some(DstLine::Smem { cell: before_cell }),
                    ..
                },
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: after_field,
                    src: Some(OperandLine::Smem { cell: after_cell }),
                    ..
                },
            ) if before_field == after_field && before_cell == after_cell
        );
        if sink && (reloads_same_source || reloads_just_stored_acc) {
            delete[instruction + 2] = true;
        }
    }

    let mut instruction = 0;
    program.instrs.retain(|_| {
        let keep = !delete[instruction];
        instruction += 1;
        keep
    });
}

#[derive(Clone, Copy)]
enum RawSourceHoistSite {
    AccLoad {
        instruction: usize,
    },
    PositiveAdd {
        instruction: usize,
        addend: OperandLine,
    },
}

/// A raw source fragment may be emitted after a destructive use of the same
/// source. Since batching addition is commutative and the sink preserves
/// `acc`, move that sink to an earlier load/use and remove the repeated read.
fn accumulator_is_dead_before_next_use(instrs: &[Instr]) -> bool {
    for instr in instrs {
        match instr {
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                ..
            } => return true,
            Instr::Mov {
                dir: MovDir::DstFromSrc,
                ..
            } => {}
            Instr::Add { .. }
            | Instr::Mul { .. }
            | Instr::Fma { .. }
            | Instr::Mov {
                dir: MovDir::DstFromAcc,
                ..
            } => return false,
        }
    }
    true
}

fn hoist_raw_source_batch_sinks(program: &mut Program) {
    loop {
        let Some((reload, source, sink)) =
            (0..program.instrs.len().saturating_sub(1)).find_map(|instruction| {
                let (
                    Instr::Mov {
                        dir: MovDir::AccFromSrc,
                        field: OperandField::Base,
                        dst: None,
                        src: Some(source),
                    },
                    Instr::Mov {
                        dir: MovDir::DstFromAcc,
                        field: OperandField::Base,
                        dst: Some(destination),
                        src: None,
                    },
                ) = (
                    &program.instrs[instruction],
                    &program.instrs[instruction + 1],
                )
                else {
                    return None;
                };
                if !matches!(
                    source,
                    OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. }
                ) || unpack_batch_dst(destination).is_none()
                    || !accumulator_is_dead_before_next_use(&program.instrs[instruction + 2..])
                {
                    return None;
                }
                let site = (0..instruction).rev().find_map(|earlier| {
                    if matches!(
                        &program.instrs[earlier],
                        Instr::Mov {
                            dir: MovDir::AccFromSrc,
                            field: OperandField::Base,
                            dst: None,
                            src: Some(earlier_source),
                        } if earlier_source == source
                    ) {
                        return Some(RawSourceHoistSite::AccLoad {
                            instruction: earlier,
                        });
                    }
                    let Some(window) = program.instrs.get(earlier..earlier + 2) else {
                        return None;
                    };
                    match (&window[0], &window[1]) {
                        (
                            Instr::Mov {
                                dir: MovDir::AccFromSrc,
                                field: OperandField::Ext,
                                dst: None,
                                src: Some(addend),
                            },
                            Instr::Add {
                                field: OperandField::Base,
                                sign: Sign::Plus,
                                promote: false,
                                operands,
                            },
                        ) if operands.as_slice() == [*source] => {
                            Some(RawSourceHoistSite::PositiveAdd {
                                instruction: earlier,
                                addend: *addend,
                            })
                        }
                        _ => None,
                    }
                })?;
                Some((instruction, site, program.instrs[instruction + 1].clone()))
            })
        else {
            break;
        };

        program.instrs.drain(reload..reload + 2);
        match source {
            RawSourceHoistSite::AccLoad { instruction } => {
                program.instrs.insert(instruction + 1, sink);
            }
            RawSourceHoistSite::PositiveAdd {
                instruction,
                addend,
            } => {
                let source = match &program.instrs[instruction + 1] {
                    Instr::Add { operands, .. } => operands[0],
                    _ => unreachable!("hoist site was matched as a positive add"),
                };
                program.instrs.splice(
                    instruction..instruction + 2,
                    [
                        Instr::Mov {
                            dir: MovDir::AccFromSrc,
                            field: OperandField::Base,
                            dst: None,
                            src: Some(source),
                        },
                        sink,
                        Instr::Add {
                            field: OperandField::Ext,
                            sign: Sign::Plus,
                            promote: true,
                            operands: vec![addend],
                        },
                    ],
                );
            }
        }
    }
}

fn smem_operand_overlaps(
    operand: OperandLine,
    operand_field: OperandField,
    stored_cell: u16,
    stored_field: OperandField,
) -> bool {
    let OperandLine::Smem { cell: operand_cell } = operand else {
        return false;
    };
    let width = |field| match field {
        OperandField::Base => 1,
        OperandField::Ext => 4,
    };
    let operand_end = operand_cell + width(operand_field);
    let stored_end = stored_cell + width(stored_field);
    operand_cell < stored_end && stored_cell < operand_end
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct StorageId(u32);

#[derive(Clone, Copy)]
struct Interval {
    id: StorageId,
    field: FieldKind,
    start: usize,
    end: usize,
}

/// Precomputed BF interval graph used by bounded exact placement. A lane's
/// assigned BF values and each value's conflicts share this dense bitset
/// representation, so a fit check is a handful of word intersections rather
/// than a scan of every interval already assigned to that lane.
struct BaseConflictGraph {
    words: usize,
    conflicts: Vec<Box<[u64]>>,
}

impl BaseConflictGraph {
    fn new(bases: &[Interval]) -> Self {
        let words = bases.len().div_ceil(u64::BITS as usize);
        let mut conflicts = vec![vec![0u64; words].into_boxed_slice(); bases.len()];
        for left in 0..bases.len() {
            for right in left + 1..bases.len() {
                if overlap(bases[left], bases[right]) {
                    set_bit(&mut conflicts[left], right);
                    set_bit(&mut conflicts[right], left);
                }
            }
        }
        Self { words, conflicts }
    }
}

fn set_bit(words: &mut [u64], index: usize) {
    words[index / u64::BITS as usize] |= 1 << (index % u64::BITS as usize);
}

fn clear_bit(words: &mut [u64], index: usize) {
    words[index / u64::BITS as usize] &= !(1 << (index % u64::BITS as usize));
}

fn intersects(left: &[u64], right: &[u64]) -> bool {
    left.iter()
        .zip(right)
        .any(|(&left, &right)| left & right != 0)
}

struct LifetimeAnalysis {
    intervals: Vec<Interval>,
    definition_at: HashMap<usize, StorageId>,
}

fn analyze_lifetimes(
    plan: &PackedEvalPlan,
    source_mode: ConcreteSourceMode<'_>,
) -> Result<LifetimeAnalysis, ConcreteBindError> {
    let mut intervals = Vec::<Interval>::new();
    let mut definition_at = HashMap::new();
    let mut residents = HashMap::<ValueFingerprint, StorageId>::new();
    let mut temps = HashMap::<TempId, StorageId>::new();

    for (op_index, op) in plan.ops.iter().enumerate() {
        let time = 2 * op_index;
        for operand in packed_operands(op) {
            match operand {
                Operand::Source(_) | Operand::Unit { .. } => {}
                Operand::BackwardSpecial { desc } => {
                    if matches!(source_mode, ConcreteSourceMode::Forward) {
                        return Err(ConcreteBindError::BackwardSpecialRequiresBindings { desc });
                    }
                }
                Operand::Resident(value) => {
                    let id = *residents
                        .get(&value.fingerprint)
                        .ok_or(ConcreteBindError::MissingResident(value.fingerprint))?;
                    interval_mut(&mut intervals, id).end = time;
                }
                Operand::Temp(temp) => {
                    let id = temps
                        .remove(&temp.id)
                        .ok_or(ConcreteBindError::MissingTemp(temp.id))?;
                    interval_mut(&mut intervals, id).end = time;
                }
            }
        }
        match op {
            PackedEvalOp::SaveAcc(temp) => {
                if temps.contains_key(&temp.id) {
                    return Err(ConcreteBindError::DuplicateTemp(temp.id));
                }
                let id = StorageId(intervals.len() as u32);
                intervals.push(Interval {
                    id,
                    field: temp.field,
                    start: time,
                    end: time,
                });
                temps.insert(temp.id, id);
                definition_at.insert(op_index, id);
            }
            PackedEvalOp::CacheStore { value, .. } => {
                if residents.contains_key(&value.fingerprint) {
                    return Err(ConcreteBindError::DuplicateResident(value.fingerprint));
                }
                let id = StorageId(intervals.len() as u32);
                intervals.push(Interval {
                    id,
                    field: value.field,
                    start: time,
                    end: time,
                });
                residents.insert(value.fingerprint, id);
                definition_at.insert(op_index, id);
            }
            PackedEvalOp::CacheDrop(value) => {
                residents
                    .remove(&value.fingerprint)
                    .ok_or(ConcreteBindError::MissingDroppedResident(value.fingerprint))?;
            }
            _ => {}
        }
    }
    if !temps.is_empty() {
        let mut live: Vec<_> = temps.keys().copied().collect();
        live.sort_by_key(|temp| temp.0);
        return Err(ConcreteBindError::LiveTempsAtEnd(live));
    }
    let end = 2 * plan.ops.len();
    for id in residents.values().copied() {
        interval_mut(&mut intervals, id).end = end;
    }
    Ok(LifetimeAnalysis {
        intervals,
        definition_at,
    })
}

fn interval_mut(intervals: &mut [Interval], id: StorageId) -> &mut Interval {
    &mut intervals[id.0 as usize]
}

fn packed_operands(op: &PackedEvalOp) -> Vec<Operand> {
    match op {
        PackedEvalOp::AccInit(operand) => vec![*operand],
        PackedEvalOp::AccAdd { operands, .. } | PackedEvalOp::AccMul { operands, .. } => {
            operands.clone()
        }
        PackedEvalOp::AccFma { pairs, .. } => {
            pairs.iter().flat_map(|&(lhs, rhs)| [lhs, rhs]).collect()
        }
        PackedEvalOp::SaveAcc(_)
        | PackedEvalOp::CacheStore { .. }
        | PackedEvalOp::CacheDrop(_)
        | PackedEvalOp::Commit { .. }
        | PackedEvalOp::BatchAccumulate { .. }
        | PackedEvalOp::ReturnBatch { .. }
        | PackedEvalOp::ReturnAcc { .. } => Vec::new(),
    }
}

fn overlap(a: Interval, b: Interval) -> bool {
    a.start <= b.end && b.start <= a.end
}

fn peak_live_lanes(intervals: &[Interval]) -> usize {
    let end = intervals
        .iter()
        .map(|interval| interval.end)
        .max()
        .unwrap_or(0);
    (0..=end)
        .map(|time| {
            intervals
                .iter()
                .filter(|interval| interval.start <= time && time <= interval.end)
                .map(|interval| field_lanes(interval.field))
                .sum()
        })
        .max()
        .unwrap_or(0)
}

fn place_intervals(
    intervals: &[Interval],
    budget: usize,
    mode: PlacementMode,
) -> Result<(HashMap<StorageId, u16>, PlacementTelemetry), PlacementTelemetry> {
    let mut locations = HashMap::new();
    let mut ext_by_quad: Vec<Vec<Interval>> = vec![Vec::new(); budget / 4];
    let mut exts: Vec<_> = intervals
        .iter()
        .copied()
        .filter(|interval| interval.field == FieldKind::Ext)
        .collect();
    exts.sort_by_key(|interval| (interval.start, interval.id.0));
    let mut greedy_ext_ok = true;
    for interval in exts {
        let Some(quad) = ext_by_quad
            .iter()
            .position(|assigned| assigned.iter().all(|other| !overlap(interval, *other)))
        else {
            greedy_ext_ok = false;
            break;
        };
        ext_by_quad[quad].push(interval);
        locations.insert(interval.id, (quad * 4) as u16);
    }

    let mut bases: Vec<_> = intervals
        .iter()
        .copied()
        .filter(|interval| interval.field == FieldKind::Base)
        .collect();
    bases.sort_by_key(|interval| (interval.start, interval.id.0));
    if greedy_ext_ok {
        if let Some(base_locations) = pack_base_intervals_greedy(&bases, &ext_by_quad, budget) {
            locations.extend(base_locations);
            return Ok((locations, PlacementTelemetry::default()));
        }
    }
    if matches!(mode, PlacementMode::GreedyOnly) {
        return Err(PlacementTelemetry::default());
    }

    let mut telemetry = PlacementTelemetry {
        exact_attempted: true,
        ..PlacementTelemetry::default()
    };
    let base_conflicts = BaseConflictGraph::new(&bases);
    if greedy_ext_ok {
        let mut base_nodes = 1_000_000u64;
        if let Some(base_locations) = pack_base_intervals_bounded(
            &bases,
            &base_conflicts,
            &ext_by_quad,
            budget,
            &mut base_nodes,
        ) {
            telemetry.base_nodes += 1_000_000 - base_nodes;
            locations.extend(base_locations);
            return Ok((locations, telemetry));
        }
        telemetry.base_nodes += 1_000_000 - base_nodes;
    }

    let mut searched_locations = HashMap::new();
    let mut searched_quads = vec![Vec::new(); budget / 4];
    let mut ext_nodes = 200_000u64;
    // This budget is shared across every complete E4 placement considered by
    // the fallback. Resetting a million-node BF search at each E4 leaf makes a
    // nominally bounded placement attempt multiplicative and effectively
    // unbounded on production-sized interval sets.
    let mut base_nodes = 1_000_000u64;
    let placed = search_ext_placement(
        0,
        &exts_for_search(intervals),
        &bases,
        &base_conflicts,
        budget,
        &mut searched_quads,
        &mut searched_locations,
        &mut ext_nodes,
        &mut base_nodes,
    );
    telemetry.ext_nodes += 200_000 - ext_nodes;
    telemetry.base_nodes += 1_000_000 - base_nodes;
    if placed {
        Ok((searched_locations, telemetry))
    } else {
        Err(telemetry)
    }
}

/// Pathological fallback for a width-feasible plan whose fixed BF intervals
/// cannot be colored around the already-fixed E4 quads. E4 locations remain
/// relocation-free. At each later E4 definition, only live BF values occupying
/// its quad are moved into currently free BF lanes.
fn place_intervals_with_relocation(
    intervals: &[Interval],
    budget: usize,
) -> Option<PhysicalPlacement> {
    if peak_live_lanes(intervals) > budget {
        return None;
    }

    let mut exts = intervals
        .iter()
        .copied()
        .filter(|interval| interval.field == FieldKind::Ext)
        .collect::<Vec<_>>();
    exts.sort_by_key(|interval| (interval.start, interval.id.0));
    let mut ext_by_quad = vec![Vec::<Interval>::new(); budget / 4];
    let mut ext_locations = HashMap::new();
    for interval in exts {
        let quad = ext_by_quad
            .iter()
            .position(|assigned| assigned.iter().all(|other| !overlap(interval, *other)))?;
        ext_by_quad[quad].push(interval);
        ext_locations.insert(interval.id, (quad * 4) as u16);
    }

    let mut ordered = intervals.to_vec();
    ordered.sort_by_key(|interval| (interval.start, interval.id.0));
    let mut definition_locations = ext_locations.clone();
    let mut moves_at = HashMap::<usize, Vec<StorageMove>>::new();
    let mut active_bases = HashMap::<StorageId, (u16, usize)>::new();

    for interval in ordered {
        let time = interval.start;
        debug_assert_eq!(
            time % 2,
            0,
            "storage definitions occur at packed-op boundaries"
        );
        active_bases.retain(|_, (_, end)| *end >= time);

        let mut forbidden = vec![false; budget];
        for ext in intervals.iter().filter(|candidate| {
            candidate.field == FieldKind::Ext && candidate.start <= time && time <= candidate.end
        }) {
            let start = ext_locations[&ext.id] as usize;
            forbidden[start..start + 4].fill(true);
        }

        let mut displaced = active_bases
            .iter()
            .filter_map(|(&id, &(lane, _))| forbidden[lane as usize].then_some(id))
            .collect::<Vec<_>>();
        displaced.sort();
        let displaced_set = displaced.iter().copied().collect::<HashSet<_>>();
        let mut occupied = vec![false; budget];
        for (&id, &(lane, _)) in &active_bases {
            if !displaced_set.contains(&id) {
                occupied[lane as usize] = true;
            }
        }
        for id in displaced {
            let (from, end) = active_bases[&id];
            let to = choose_base_lane(
                budget,
                &forbidden,
                &occupied,
                time,
                end,
                intervals,
                &ext_locations,
            )?;
            occupied[to as usize] = true;
            active_bases.insert(id, (to, end));
            moves_at
                .entry(time / 2)
                .or_default()
                .push(StorageMove { id, from, to });
        }

        if interval.field == FieldKind::Base {
            let lane = choose_base_lane(
                budget,
                &forbidden,
                &occupied,
                time,
                interval.end,
                intervals,
                &ext_locations,
            )?;
            definition_locations.insert(interval.id, lane);
            active_bases.insert(interval.id, (lane, interval.end));
        }
    }

    Some(PhysicalPlacement {
        definition_locations,
        moves_at,
    })
}

fn choose_base_lane(
    budget: usize,
    forbidden: &[bool],
    occupied: &[bool],
    time: usize,
    end: usize,
    intervals: &[Interval],
    ext_locations: &HashMap<StorageId, u16>,
) -> Option<u16> {
    (0..budget)
        .filter(|&lane| !forbidden[lane] && !occupied[lane])
        .max_by_key(|&lane| {
            let next_conflict = intervals
                .iter()
                .filter(|interval| interval.field == FieldKind::Ext)
                .filter(|interval| ext_locations[&interval.id] as usize / 4 == lane / 4)
                .filter(|interval| time < interval.start && interval.start <= end)
                .map(|interval| interval.start)
                .min()
                .unwrap_or(usize::MAX);
            (next_conflict, std::cmp::Reverse(lane))
        })
        .map(|lane| lane as u16)
}

fn exts_for_search(intervals: &[Interval]) -> Vec<Interval> {
    let mut exts = intervals
        .iter()
        .copied()
        .filter(|interval| interval.field == FieldKind::Ext)
        .collect::<Vec<_>>();
    exts.sort_by_key(|interval| (interval.start, interval.id.0));
    exts
}

fn pack_base_intervals_bounded(
    bases: &[Interval],
    conflicts: &BaseConflictGraph,
    ext_by_quad: &[Vec<Interval>],
    budget: usize,
    nodes: &mut u64,
) -> Option<HashMap<StorageId, u16>> {
    if let Some(locations) = pack_base_intervals_greedy(bases, ext_by_quad, budget) {
        return Some(locations);
    }
    let mut allowed_lanes = vec![0u64; bases.len()];
    for (index, &interval) in bases.iter().enumerate() {
        for lane in 0..budget {
            let ext_clear = ext_by_quad
                .get(lane / 4)
                .is_none_or(|assigned| assigned.iter().all(|other| !overlap(interval, *other)));
            if ext_clear {
                allowed_lanes[index] |= 1 << lane;
            }
        }
        if allowed_lanes[index] == 0 {
            return None;
        }
    }

    let mut remaining = (0..bases.len()).collect::<Vec<_>>();
    let mut assigned_by_lane = vec![vec![0u64; conflicts.words].into_boxed_slice(); budget];
    let mut assignments = vec![None; bases.len()];
    if !search_base_placement(
        bases,
        conflicts,
        &mut remaining,
        &allowed_lanes,
        ext_by_quad,
        &mut assigned_by_lane,
        &mut assignments,
        nodes,
    ) {
        return None;
    }
    Some(
        bases
            .iter()
            .zip(assignments)
            .map(|(interval, lane)| {
                (
                    interval.id,
                    lane.expect("complete exact BF placement has every assignment"),
                )
            })
            .collect(),
    )
}

fn pack_base_intervals_greedy(
    bases: &[Interval],
    ext_by_quad: &[Vec<Interval>],
    budget: usize,
) -> Option<HashMap<StorageId, u16>> {
    let mut locations = HashMap::new();
    let mut bases_by_lane: Vec<Vec<Interval>> = vec![Vec::new(); budget];
    for &interval in bases {
        let lane = (0..budget)
            .find(|&lane| base_fits_lane(interval, lane, ext_by_quad, &bases_by_lane))?;
        bases_by_lane[lane].push(interval);
        locations.insert(interval.id, lane as u16);
    }
    Some(locations)
}

fn base_fits_lane(
    interval: Interval,
    lane: usize,
    ext_by_quad: &[Vec<Interval>],
    bases_by_lane: &[Vec<Interval>],
) -> bool {
    let ext_clear = ext_by_quad
        .get(lane / 4)
        .is_none_or(|assigned| assigned.iter().all(|other| !overlap(interval, *other)));
    ext_clear
        && bases_by_lane[lane]
            .iter()
            .all(|other| !overlap(interval, *other))
}

fn search_base_placement(
    bases: &[Interval],
    conflicts: &BaseConflictGraph,
    remaining: &mut Vec<usize>,
    allowed_lanes: &[u64],
    ext_by_quad: &[Vec<Interval>],
    assigned_by_lane: &mut [Box<[u64]>],
    assignments: &mut [Option<u16>],
    nodes: &mut u64,
) -> bool {
    if *nodes == 0 {
        return false;
    }
    *nodes -= 1;
    if remaining.is_empty() {
        return true;
    }

    let mut choice = None::<(usize, u64, (u32, std::cmp::Reverse<usize>, StorageId))>;
    for (remaining_index, &base_index) in remaining.iter().enumerate() {
        let interval = bases[base_index];
        let mut lanes = allowed_lanes[base_index];
        let mut candidates = lanes;
        while candidates != 0 {
            let lane = candidates.trailing_zeros() as usize;
            candidates &= candidates - 1;
            if intersects(&conflicts.conflicts[base_index], &assigned_by_lane[lane]) {
                lanes &= !(1 << lane);
            }
        }
        if lanes == 0 {
            return false;
        }
        let key = (
            lanes.count_ones(),
            std::cmp::Reverse(interval.end - interval.start),
            interval.id,
        );
        if choice
            .as_ref()
            .is_none_or(|(_, _, best_key)| key < *best_key)
        {
            choice = Some((remaining_index, lanes, key));
        }
    }
    let (index, mut lanes, _) = choice.expect("non-empty remaining set has a choice");
    let base_index = remaining.swap_remove(index);

    let mut tried_lanes = 0u64;
    while lanes != 0 {
        let lane = lanes.trailing_zeros() as usize;
        lanes &= lanes - 1;
        let symmetric = (0..assigned_by_lane.len()).any(|previous| {
            tried_lanes & (1 << previous) != 0
                && ext_by_quad
                    .get(lane / 4)
                    .into_iter()
                    .flatten()
                    .map(|interval| interval.id)
                    .eq(ext_by_quad
                        .get(previous / 4)
                        .into_iter()
                        .flatten()
                        .map(|interval| interval.id))
                && assigned_by_lane[lane] == assigned_by_lane[previous]
        });
        if symmetric {
            continue;
        }
        tried_lanes |= 1 << lane;

        set_bit(&mut assigned_by_lane[lane], base_index);
        assignments[base_index] = Some(lane as u16);
        if search_base_placement(
            bases,
            conflicts,
            remaining,
            allowed_lanes,
            ext_by_quad,
            assigned_by_lane,
            assignments,
            nodes,
        ) {
            return true;
        }
        clear_bit(&mut assigned_by_lane[lane], base_index);
        assignments[base_index] = None;
    }
    remaining.push(base_index);
    false
}

#[allow(clippy::too_many_arguments)]
fn search_ext_placement(
    index: usize,
    exts: &[Interval],
    bases: &[Interval],
    base_conflicts: &BaseConflictGraph,
    budget: usize,
    quads: &mut Vec<Vec<Interval>>,
    locations: &mut HashMap<StorageId, u16>,
    ext_nodes: &mut u64,
    base_nodes: &mut u64,
) -> bool {
    if *ext_nodes == 0 || *base_nodes == 0 {
        return false;
    }
    *ext_nodes -= 1;
    if index == exts.len() {
        if let Some(base_locations) =
            pack_base_intervals_bounded(bases, base_conflicts, quads, budget, base_nodes)
        {
            locations.extend(base_locations);
            return true;
        }
        return false;
    }

    let interval = exts[index];
    let mut candidates = (0..quads.len())
        .filter(|&quad| quads[quad].iter().all(|other| !overlap(interval, *other)))
        .collect::<Vec<_>>();
    candidates.sort_by_key(|&quad| {
        (
            std::cmp::Reverse(quads[quad].iter().map(|other| other.end).max()),
            quad,
        )
    });
    let mut signatures = HashSet::<Vec<StorageId>>::new();
    candidates
        .retain(|&quad| signatures.insert(quads[quad].iter().map(|other| other.id).collect()));
    for quad in candidates {
        quads[quad].push(interval);
        locations.insert(interval.id, (quad * 4) as u16);
        if search_ext_placement(
            index + 1,
            exts,
            bases,
            base_conflicts,
            budget,
            quads,
            locations,
            ext_nodes,
            base_nodes,
        ) {
            return true;
        }
        quads[quad].pop();
        locations.remove(&interval.id);
    }
    false
}

struct Emitter<'a> {
    layer: &'a DagLayer,
    this_layer: usize,
    fingerprints: Vec<ValueFingerprint>,
    lifetimes: &'a LifetimeAnalysis,
    definition_locations: &'a HashMap<StorageId, u16>,
    moves_at: &'a HashMap<usize, Vec<StorageMove>>,
    current_locations: HashMap<StorageId, u16>,
    ctx: DagForwardContext,
    instrs: Vec<Instr>,
    residents: HashMap<ValueFingerprint, StorageId>,
    temps: HashMap<TempId, StorageId>,
    pending_roots: HashSet<RootId>,
    root_outputs: Vec<(RootId, RootOutput)>,
    terminal: Option<PendingTerminal>,
    batch_sinks: usize,
    desc_by_expr: HashMap<gkr_eval_ir::ExprId, u16>,
    source_mode: ConcreteSourceMode<'a>,
}

enum PendingTerminal {
    ReturnAcc(RootKey),
    ReturnBatch(RootKey),
}

impl PendingTerminal {
    fn root(&self) -> &RootKey {
        match self {
            Self::ReturnAcc(root) | Self::ReturnBatch(root) => root,
        }
    }
}

impl Emitter<'_> {
    fn emit(&mut self, op_index: usize, op: &PackedEvalOp) -> Result<(), ConcreteBindError> {
        if let Some(terminal) = &self.terminal {
            let repeats_same_terminal = matches!(
                (terminal, op),
                (
                    PendingTerminal::ReturnAcc(_),
                    PackedEvalOp::ReturnAcc { .. }
                ) | (
                    PendingTerminal::ReturnBatch(_),
                    PackedEvalOp::ReturnBatch { .. }
                )
            );
            if !repeats_same_terminal {
                return Err(ConcreteBindError::MixedForwardAndReturnTerminal);
            }
        }
        self.emit_relocations(op_index)?;
        match op {
            PackedEvalOp::AccInit(operand) => {
                let src = self.bind_operand(*operand)?;
                self.instrs.push(Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: operand_field(*operand),
                    dst: None,
                    src: Some(src),
                });
            }
            PackedEvalOp::AccAdd {
                field,
                promote,
                sign,
                operands,
            } => {
                let bound = operands
                    .iter()
                    .map(|&operand| self.bind_operand(operand))
                    .collect::<Result<_, _>>()?;
                self.instrs.push(Instr::Add {
                    field: to_operand_field(*field),
                    sign: *sign,
                    promote: *promote,
                    operands: bound,
                });
            }
            PackedEvalOp::AccMul {
                field,
                promote,
                sign,
                operands,
            } => {
                operands
                    .iter()
                    .try_for_each(|&operand| self.reject_multiplication_by_one(operand))?;
                let bound = operands
                    .iter()
                    .map(|&operand| self.bind_operand(operand))
                    .collect::<Result<_, _>>()?;
                self.instrs.push(Instr::Mul {
                    field: to_operand_field(*field),
                    promote: *promote,
                    negate_acc: *sign == Sign::Minus,
                    operands: bound,
                });
            }
            PackedEvalOp::AccFma {
                field_lhs,
                field_rhs,
                promote,
                sign,
                pairs,
            } => {
                pairs.iter().try_for_each(|&(lhs, rhs)| {
                    self.reject_multiplication_by_one(lhs)?;
                    self.reject_multiplication_by_one(rhs)
                })?;
                let bound = pairs
                    .iter()
                    .map(|&(lhs, rhs)| Ok((self.bind_operand(lhs)?, self.bind_operand(rhs)?)))
                    .collect::<Result<_, ConcreteBindError>>()?;
                self.instrs.push(Instr::Fma {
                    field_lhs: to_operand_field(*field_lhs),
                    field_rhs: to_operand_field(*field_rhs),
                    sign: *sign,
                    promote: *promote,
                    pairs: bound,
                });
            }
            PackedEvalOp::SaveAcc(temp) => {
                let id = self.definition(op_index)?;
                self.temps.insert(temp.id, id);
                self.current_locations
                    .insert(id, self.definition_locations[&id]);
                self.instrs.push(Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: to_operand_field(temp.field),
                    dst: Some(self.storage_dst(id, temp.field)),
                    src: None,
                });
            }
            PackedEvalOp::CacheStore { value, from } => {
                let id = self.definition(op_index)?;
                self.residents.insert(value.fingerprint, id);
                self.current_locations
                    .insert(id, self.definition_locations[&id]);
                let dst = Some(self.storage_dst(id, value.field));
                let instruction = match from {
                    CacheStoreFrom::Acc => Instr::Mov {
                        dir: MovDir::DstFromAcc,
                        field: to_operand_field(value.field),
                        dst,
                        src: None,
                    },
                    CacheStoreFrom::Source => Instr::Mov {
                        dir: MovDir::DstFromSrc,
                        field: to_operand_field(value.field),
                        dst,
                        src: Some(self.bind_source(*value)?),
                    },
                };
                self.instrs.push(instruction);
            }
            PackedEvalOp::CacheDrop(value) => {
                let id = self
                    .residents
                    .remove(&value.fingerprint)
                    .ok_or(ConcreteBindError::MissingDroppedResident(value.fingerprint))?;
                self.current_locations.remove(&id);
            }
            PackedEvalOp::Commit {
                root_id,
                root,
                sink,
                from,
            } => {
                if matches!(self.source_mode, ConcreteSourceMode::Backward { .. }) {
                    return Err(ConcreteBindError::BackwardCommit);
                }
                self.emit_commit(*root_id, root, sink, *from)?;
            }
            PackedEvalOp::BatchAccumulate {
                coefficient_desc,
                field,
            } => {
                if matches!(self.source_mode, ConcreteSourceMode::Forward) {
                    return Err(ConcreteBindError::BatchAccumulateRequiresBackwardMode);
                }
                let coefficient = match coefficient_desc {
                    Some(desc) if *desc <= BATCH_COEFFICIENT_MAX => *desc,
                    Some(desc) => {
                        return Err(ConcreteBindError::InvalidBatchCoefficientDescriptor {
                            desc: *desc,
                        });
                    }
                    None => BATCH_COEFFICIENT_ONE,
                };
                self.instrs.push(Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: to_operand_field(*field),
                    dst: Some(pack_batch_dst(coefficient).map_err(|_| {
                        ConcreteBindError::InvalidBatchCoefficientDescriptor { desc: coefficient }
                    })?),
                    src: None,
                });
                self.batch_sinks += 1;
            }
            PackedEvalOp::ReturnBatch { root } => {
                if matches!(self.source_mode, ConcreteSourceMode::Forward) {
                    return Err(ConcreteBindError::ReturnBatchRequiresBackwardMode);
                }
                if self
                    .terminal
                    .replace(PendingTerminal::ReturnBatch(root.clone()))
                    .is_some()
                {
                    return Err(ConcreteBindError::DuplicateReturnBatch);
                }
            }
            PackedEvalOp::ReturnAcc { root } => {
                if matches!(self.source_mode, ConcreteSourceMode::Backward { .. }) {
                    return Err(ConcreteBindError::MissingReturnBatch);
                }
                if self
                    .terminal
                    .replace(PendingTerminal::ReturnAcc(root.clone()))
                    .is_some()
                {
                    return Err(ConcreteBindError::DuplicateReturnAcc);
                }
            }
        }
        Ok(())
    }

    fn emit_relocations(&mut self, op_index: usize) -> Result<(), ConcreteBindError> {
        let Some(moves) = self.moves_at.get(&op_index) else {
            return Ok(());
        };
        for relocation in moves {
            let actual = self
                .current_locations
                .get(&relocation.id)
                .copied()
                .ok_or(ConcreteBindError::MissingStorageLocation(relocation.id.0))?;
            if actual != relocation.from {
                return Err(ConcreteBindError::RelocationSourceMismatch {
                    id: relocation.id.0,
                    expected: relocation.from,
                    actual,
                });
            }
            self.instrs.push(Instr::Mov {
                dir: MovDir::DstFromSrc,
                field: OperandField::Base,
                dst: Some(DstLine::Smem {
                    cell: relocation.to,
                }),
                src: Some(OperandLine::Smem {
                    cell: relocation.from,
                }),
            });
            self.current_locations.insert(relocation.id, relocation.to);
        }
        Ok(())
    }

    fn definition(&self, op_index: usize) -> Result<StorageId, ConcreteBindError> {
        self.lifetimes
            .definition_at
            .get(&op_index)
            .copied()
            .ok_or(ConcreteBindError::MissingDefinition(op_index))
    }

    fn bind_operand(&mut self, operand: Operand) -> Result<OperandLine, ConcreteBindError> {
        match operand {
            Operand::Source(value) => self.bind_source(value),
            Operand::Resident(value) => {
                let id = *self
                    .residents
                    .get(&value.fingerprint)
                    .ok_or(ConcreteBindError::MissingResident(value.fingerprint))?;
                self.storage_operand(id, value.field)
            }
            Operand::Temp(temp) => {
                let id = self
                    .temps
                    .remove(&temp.id)
                    .ok_or(ConcreteBindError::MissingTemp(temp.id))?;
                let operand = self.storage_operand(id, temp.field)?;
                self.current_locations.remove(&id);
                Ok(operand)
            }
            Operand::Unit { negative } => Ok(OperandLine::Ldc {
                sub: LdcSub::Special,
                idx: if negative {
                    Special::NegOne as u16
                } else {
                    Special::One as u16
                },
            }),
            Operand::BackwardSpecial { desc } => match self.source_mode {
                ConcreteSourceMode::Forward => {
                    Err(ConcreteBindError::BackwardSpecialRequiresBindings { desc })
                }
                ConcreteSourceMode::Backward { .. } => Ok(OperandLine::Special { desc }),
            },
        }
    }

    fn reject_multiplication_by_one(&self, operand: Operand) -> Result<(), ConcreteBindError> {
        let value = match operand {
            Operand::Source(value) | Operand::Resident(value) => value,
            Operand::Temp(_) => return Ok(()),
            Operand::Unit { negative } => {
                return Err(ConcreteBindError::MultiplicationBySyntheticUnit { negative });
            }
            Operand::BackwardSpecial { desc } => match self.source_mode {
                ConcreteSourceMode::Forward => {
                    return Err(ConcreteBindError::BackwardSpecialRequiresBindings { desc });
                }
                ConcreteSourceMode::Backward { .. } => return Ok(()),
            },
        };
        if let Some(negative) = unit_sign_expr(self.layer, value.expr) {
            return Err(if negative {
                ConcreteBindError::MultiplicationByNegOne(value.expr)
            } else {
                ConcreteBindError::MultiplicationByOne(value.expr)
            });
        }
        Ok(())
    }

    fn bind_source(&mut self, value: ValueRef) -> Result<OperandLine, ConcreteBindError> {
        let backward_source = if let ConcreteSourceMode::Backward {
            leaf_descs,
            specials,
            ..
        } = self.source_mode
        {
            leaf_descs
                .get(&value.expr)
                .copied()
                .map(|desc| (desc, specials))
        } else {
            None
        };
        if let Some((desc, specials)) = backward_source {
            if let Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(place),
            }) = specials.get(desc)
            {
                let (slot, col) = self
                    .ctx
                    .backings
                    .read_slot_col(place, to_operand_field(value.field))?;
                return Ok(OperandLine::LogicalFold { slot, col, desc });
            }
            return Ok(OperandLine::Special { desc });
        }
        if matches!(self.source_mode, ConcreteSourceMode::Forward) {
            if let Some(strategy) = self.layer.resolutions.get(&value.expr) {
                let desc =
                    self.intern_descriptor(value.expr, lower_resolution(strategy, value.expr))?;
                return Ok(OperandLine::Special { desc });
            }
        }
        let Expr::Source(source) = &self.layer.exprs[value.expr.0 as usize] else {
            return Err(ConcreteBindError::ExpectedSource(value));
        };
        Ok(match &self.layer.sources[source.0 as usize].kind {
            SourceKind::Read { place } => {
                let (slot, col) = self
                    .ctx
                    .backings
                    .read_slot_col(place, to_operand_field(value.field))?;
                OperandLine::LogicalGlobal { slot, col }
            }
            SourceKind::Constant { value: constant } => match *constant {
                0 => return Err(ConcreteBindError::UnencodableZero(value.expr)),
                1 => OperandLine::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::One as u16,
                },
                BABYBEAR_NEG_ONE => OperandLine::Ldc {
                    sub: LdcSub::Special,
                    idx: Special::NegOne as u16,
                },
                constant => OperandLine::Ldc {
                    sub: LdcSub::Const,
                    idx: self.ctx.consts.intern(constant),
                },
            },
            SourceKind::Challenge { reference } => {
                let (sub, idx) = self.ctx.derived_e4.intern(reference);
                OperandLine::Ldc { sub, idx }
            }
            SourceKind::VirtualSetup { kind } => {
                if matches!(self.source_mode, ConcreteSourceMode::Backward { .. }) {
                    return Err(ConcreteBindError::UnboundBackwardSource(value.expr));
                }
                let descriptor = SpecialDescriptor {
                    strategy: SpecialStrategy::VirtualSetup { kind: kind.clone() },
                    origin_expr: value.expr,
                };
                OperandLine::Special {
                    desc: self.intern_descriptor(value.expr, descriptor)?,
                }
            }
            SourceKind::LookupValue { .. } => {
                return Err(match self.source_mode {
                    ConcreteSourceMode::Forward => ConcreteBindError::UncoveredLookup(value),
                    ConcreteSourceMode::Backward { .. } => {
                        ConcreteBindError::UnboundBackwardSource(value.expr)
                    }
                });
            }
        })
    }

    fn intern_descriptor(
        &mut self,
        expr: gkr_eval_ir::ExprId,
        descriptor: SpecialDescriptor,
    ) -> Result<u16, ConcreteBindError> {
        if let Some(&desc) = self.desc_by_expr.get(&expr) {
            return Ok(desc);
        }
        if self.ctx.specials.len() as u32 >= MAX_DESC {
            return Err(ConcreteBindError::DescriptorOverflow);
        }
        let desc = self.ctx.specials.push(descriptor);
        self.desc_by_expr.insert(expr, desc);
        Ok(desc)
    }

    fn storage_operand(
        &self,
        id: StorageId,
        field: FieldKind,
    ) -> Result<OperandLine, ConcreteBindError> {
        let location = self
            .current_locations
            .get(&id)
            .copied()
            .ok_or(ConcreteBindError::MissingStorageLocation(id.0))?;
        Ok(OperandLine::Smem {
            cell: wire_cell(location, field),
        })
    }

    fn storage_dst(&self, id: StorageId, field: FieldKind) -> DstLine {
        DstLine::Smem {
            cell: wire_cell(self.current_locations[&id], field),
        }
    }

    fn emit_commit(
        &mut self,
        root_id: RootId,
        root: &RootKey,
        sink: &SinkInfo,
        from: MaterializeFrom,
    ) -> Result<(), ConcreteBindError> {
        if !self.pending_roots.remove(&root_id) {
            return Err(ConcreteBindError::RootIdentityMismatch { root: root_id });
        }
        let expected = root_key(self.layer, &self.fingerprints, root_id);
        if expected != *root
            || self.layer.roots[root_id.0 as usize].materialize.as_ref() != Some(sink)
        {
            return Err(ConcreteBindError::RootIdentityMismatch { root: root_id });
        }
        let (key, offset) = sink_backing(sink, self.this_layer);
        let (slot, col) = self.ctx.backings.slot_col(key, offset)?;
        let (dir, src) = match from {
            MaterializeFrom::Acc => (MovDir::DstFromAcc, None),
            MaterializeFrom::Source(value) => (MovDir::DstFromSrc, Some(self.bind_source(value)?)),
        };
        self.instrs.push(Instr::Mov {
            dir,
            field: to_operand_field(sink.field),
            dst: Some(DstLine::GlobalMaterialize { slot, col }),
            src,
        });
        self.root_outputs
            .push((root_id, RootOutput::Cell(OutputCell::Global { slot, col })));
        Ok(())
    }
}

fn wire_cell(lane: u16, field: FieldKind) -> u16 {
    match field {
        FieldKind::Base => lane,
        FieldKind::Ext => {
            debug_assert_eq!(lane % 4, 0);
            lane / 4
        }
    }
}

fn operand_field(operand: Operand) -> OperandField {
    to_operand_field(match operand {
        Operand::Source(value) | Operand::Resident(value) => value.field,
        Operand::Temp(temp) => temp.field,
        Operand::Unit { .. } => FieldKind::Base,
        Operand::BackwardSpecial { .. } => FieldKind::Ext,
    })
}

fn to_operand_field(field: FieldKind) -> OperandField {
    match field {
        FieldKind::Base => OperandField::Base,
        FieldKind::Ext => OperandField::Ext,
    }
}

fn root_key(layer: &DagLayer, fingerprints: &[ValueFingerprint], root_id: RootId) -> RootKey {
    let root = &layer.roots[root_id.0 as usize];
    RootKey {
        expr: fingerprints[root.expr.0 as usize],
        materialize: root.materialize.clone(),
        claim_origin: root.claim.as_ref().map(|claim| claim.origin.clone()),
    }
}

fn sink_backing(sink: &SinkInfo, this_layer: usize) -> (BackingKey, usize) {
    let field = to_operand_field(sink.field);
    match sink.kind {
        SinkKind::Inner { layer, offset } => (BackingKey::LayerOutput { layer, field }, offset),
        SinkKind::Cache { layer, offset } => (BackingKey::CacheOutput { layer, field }, offset),
        SinkKind::Export { slot } => (
            BackingKey::LayerOutput {
                layer: this_layer,
                field,
            },
            slot,
        ),
        SinkKind::Scratch { slot } => (BackingKey::Scratch, slot),
    }
}

fn tally_program(
    program: &Program,
    ctx: &DagForwardContext,
    max_live_lanes: usize,
) -> CompileStats {
    let mut stats = CompileStats {
        program_lanes: program.instrs.len(),
        max_live_cells: max_live_lanes,
        ..CompileStats::default()
    };
    for instr in &program.instrs {
        match instr {
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => {
                stats.op_counts[OP_MOV] += 1;
                if let Some(operand) = src {
                    tally_operand(*operand, *field, ctx, &mut stats);
                }
                if matches!(dir, MovDir::DstFromAcc | MovDir::DstFromSrc)
                    && matches!(dst, Some(DstLine::Smem { .. }))
                {
                    stats.cell_stores += 1;
                }
            }
            Instr::Add {
                field, operands, ..
            } => {
                stats.op_counts[OP_ADD] += 1;
                for &operand in operands {
                    tally_operand(operand, *field, ctx, &mut stats);
                }
            }
            Instr::Mul {
                field, operands, ..
            } => {
                stats.op_counts[OP_MUL] += 1;
                for &operand in operands {
                    tally_operand(operand, *field, ctx, &mut stats);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                stats.op_counts[OP_FMA] += 1;
                for &(lhs, rhs) in pairs {
                    tally_operand(lhs, *field_lhs, ctx, &mut stats);
                    tally_operand(rhs, *field_rhs, ctx, &mut stats);
                }
            }
        }
    }
    stats.special_gathers = ctx
        .specials
        .iter()
        .filter(|descriptor| !matches!(descriptor.strategy, SpecialStrategy::VirtualSetup { .. }))
        .count();
    stats
}

fn tally_operand(
    operand: OperandLine,
    field: OperandField,
    ctx: &DagForwardContext,
    stats: &mut CompileStats,
) {
    match operand {
        OperandLine::LogicalGlobal { .. }
        | OperandLine::LogicalFold { .. }
        | OperandLine::Source { .. } => {
            stats.dram_reads += 1;
            stats.dram_traffic += match field {
                OperandField::Base => 1,
                OperandField::Ext => 4,
            };
        }
        OperandLine::Smem { .. } => stats.cell_reads += 1,
        OperandLine::Ldc {
            sub: LdcSub::Special,
            ..
        } => {}
        OperandLine::Ldc { .. } => stats.ldc_reads += 1,
        OperandLine::Special { desc } => {
            if !matches!(
                ctx.specials
                    .get(desc)
                    .map(|descriptor| &descriptor.strategy),
                Some(SpecialStrategy::VirtualSetup { .. })
            ) {
                stats.special_reads += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::batch::{
        BATCH_COEFFICIENT_MAX, BATCH_COEFFICIENT_ONE, pack_batch_dst, unpack_batch_dst,
    };
    use crate::bwd::source::BwdSpecialTable;
    use crate::eval_plan::{
        CacheStoreFrom, EvalOp, PackConfig, PackedStats, ValueRef, elaborate_uncached, pack_plan,
        structural_fingerprints,
    };
    use crate::fwd::interp::interpret_program_row_acc;
    use cs::definitions::GKRAddress;
    use field::Field;
    use gkr_eval_ir::{
        BatchingOrder, Bf, ChallengeRef, ChallengeResolver, DagLayer, Expr, ExprId, FieldKind,
        LookupResolver, LookupValueKind, ReadPlace, ReadResolver, Resolvers, Root, RootId,
        SourceId, SourceInfo, SourceKind, VirtualSetupKind, VirtualSetupResolver, eval_layer_expr,
    };

    struct UnusedResolver;

    impl ReadResolver for UnusedResolver {
        fn read(&self, _place: &ReadPlace, _row: usize) -> gkr_eval_ir::Ext {
            unreachable!("constant-only test layer does not read")
        }
    }

    impl LookupResolver for UnusedResolver {
        fn lookup(
            &self,
            _kind: &LookupValueKind,
            _set_index: usize,
            _evaluated_query: gkr_eval_ir::Ext,
            _row: usize,
        ) -> Bf {
            unreachable!("constant-only test layer does not look up")
        }
    }

    impl VirtualSetupResolver for UnusedResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, _row: usize) -> Bf {
            unreachable!("constant-only test layer has no virtual setup")
        }
    }

    impl ChallengeResolver for UnusedResolver {
        fn challenge(&self, _reference: &ChallengeRef) -> gkr_eval_ir::Ext {
            unreachable!("constant-only test layer has no derived_e4")
        }
    }

    static UNUSED_RESOLVER: UnusedResolver = UnusedResolver;

    fn resolvers() -> Resolvers<'static> {
        Resolvers {
            read: &UNUSED_RESOLVER,
            lookup: &UNUSED_RESOLVER,
            virtual_setup: &UNUSED_RESOLVER,
            challenge: &UNUSED_RESOLVER,
        }
    }

    fn return_acc_layer(materialize_first_root: bool) -> DagLayer {
        let roots = (0..if materialize_first_root { 2 } else { 1 })
            .map(|index| Root {
                expr: ExprId(0),
                materialize: (index == 0 && materialize_first_root).then_some(SinkInfo {
                    kind: SinkKind::Export { slot: 0 },
                    field: FieldKind::Base,
                }),
                claim: None,
            })
            .collect();
        DagLayer {
            sources: vec![SourceInfo {
                kind: SourceKind::Constant { value: 42 },
            }],
            exprs: vec![Expr::Source(SourceId(0))],
            roots,
            batching: BatchingOrder { roots: vec![] },
            resolutions: Default::default(),
        }
    }

    fn return_acc_packed(layer: &DagLayer, roots: &[RootId]) -> PackedEvalPlan {
        let fields = vec![FieldKind::Base];
        let plan = elaborate_uncached(layer, &fields, roots).unwrap();
        pack_plan(&plan, layer, PackConfig::default()).unwrap()
    }

    fn batch_packed(
        layer: &DagLayer,
        coefficient_desc: Option<u16>,
        field: FieldKind,
    ) -> PackedEvalPlan {
        let fields = vec![FieldKind::Base];
        let mut plan = elaborate_uncached(layer, &fields, &[RootId(0)]).unwrap();
        let EvalOp::ReturnAcc { root } = plan.ops.pop().unwrap() else {
            panic!("fixture must end in ReturnAcc");
        };
        plan.ops.push(EvalOp::BatchAccumulate {
            coefficient_desc,
            field,
        });
        plan.ops.push(EvalOp::ReturnBatch { root });
        plan.stats.arithmetic_ops += 1;
        pack_plan(&plan, layer, PackConfig::default()).unwrap()
    }

    #[test]
    fn backward_batch_sink_emits_exact_carrier_and_recovers_descriptor() {
        let layer = return_acc_layer(false);
        let packed = batch_packed(&layer, Some(17), FieldKind::Base);
        let concrete = bind_backward_packed_plan(
            &packed,
            &layer,
            RootId(0),
            4,
            &BTreeMap::new(),
            &BwdSpecialTable::default(),
        )
        .unwrap();

        assert!(matches!(
            concrete.terminal,
            ConcreteTerminal::ReturnBatch { .. }
        ));
        let sink = concrete.compiled.program.instrs.last().unwrap();
        let Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(dst),
            src: None,
        } = sink
        else {
            panic!("expected exact Base DstFromAcc batch carrier, got {sink:?}");
        };
        assert_eq!(unpack_batch_dst(dst), Some(17));
        assert_eq!(
            encode(&Program {
                instrs: vec![sink.clone()],
            })
            .unwrap()
            .len(),
            2
        );
    }

    #[test]
    fn backward_batch_sink_uses_literal_one_sentinel_and_exact_ext_field() {
        let layer = return_acc_layer(false);
        let packed = batch_packed(&layer, None, FieldKind::Ext);
        let concrete = bind_backward_packed_plan(
            &packed,
            &layer,
            RootId(0),
            4,
            &BTreeMap::new(),
            &BwdSpecialTable::default(),
        )
        .unwrap();

        assert!(matches!(
            concrete.compiled.program.instrs.last(),
            Some(Instr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Ext,
                dst: Some(dst),
                src: None,
            }) if unpack_batch_dst(dst) == Some(BATCH_COEFFICIENT_ONE)
        ));
    }

    #[test]
    fn backward_batch_sink_rejects_reserved_and_out_of_range_descriptors() {
        let layer = return_acc_layer(false);
        for desc in [BATCH_COEFFICIENT_ONE, 0x4000] {
            let packed = batch_packed(&layer, Some(desc), FieldKind::Base);
            assert!(matches!(
                bind_backward_packed_plan(
                    &packed,
                    &layer,
                    RootId(0),
                    4,
                    &BTreeMap::new(),
                    &BwdSpecialTable::default(),
                ),
                Err(ConcreteBindError::InvalidBatchCoefficientDescriptor { desc: actual })
                    if actual == desc
            ));
        }
        assert_eq!(BATCH_COEFFICIENT_MAX, 0x3ffe);
    }

    #[test]
    fn forward_mode_rejects_batch_sinks_and_terminal() {
        let layer = return_acc_layer(false);
        let packed = batch_packed(&layer, None, FieldKind::Base);
        assert!(matches!(
            bind_packed_plan(&packed, &layer, &[RootId(0)], 0, 4),
            Err(ConcreteBindError::BatchAccumulateRequiresBackwardMode)
                | Err(ConcreteBindError::ReturnBatchRequiresBackwardMode)
        ));
    }

    #[test]
    fn backward_mode_does_not_accept_return_acc_as_return_batch() {
        let layer = return_acc_layer(false);
        let packed = return_acc_packed(&layer, &[RootId(0)]);

        assert!(matches!(
            bind_backward_packed_plan(
                &packed,
                &layer,
                RootId(0),
                4,
                &BTreeMap::new(),
                &BwdSpecialTable::default(),
            ),
            Err(ConcreteBindError::MissingReturnBatch)
        ));
    }

    #[test]
    fn backward_mode_requires_exactly_one_return_batch() {
        let layer = return_acc_layer(false);
        let mut missing = batch_packed(&layer, None, FieldKind::Base);
        assert!(matches!(
            missing.ops.pop(),
            Some(PackedEvalOp::ReturnBatch { .. })
        ));
        assert!(matches!(
            bind_backward_packed_plan(
                &missing,
                &layer,
                RootId(0),
                4,
                &BTreeMap::new(),
                &BwdSpecialTable::default(),
            ),
            Err(ConcreteBindError::MissingReturnBatch)
        ));

        let mut duplicate = batch_packed(&layer, None, FieldKind::Base);
        duplicate.ops.push(duplicate.ops.last().unwrap().clone());
        assert!(matches!(
            bind_backward_packed_plan(
                &duplicate,
                &layer,
                RootId(0),
                4,
                &BTreeMap::new(),
                &BwdSpecialTable::default(),
            ),
            Err(ConcreteBindError::DuplicateReturnBatch)
        ));
    }

    #[test]
    fn batch_sink_preserves_acc_and_elides_resident_reload() {
        let layer = return_acc_layer(false);
        let fingerprint = structural_fingerprints(&layer).unwrap()[0];
        let value = ValueRef {
            fingerprint,
            expr: ExprId(0),
            field: FieldKind::Base,
        };
        let root = match return_acc_packed(&layer, &[RootId(0)]).ops.last().unwrap() {
            PackedEvalOp::ReturnAcc { root } => root.clone(),
            other => panic!("fixture must end in ReturnAcc, got {other:?}"),
        };
        let packed = PackedEvalPlan {
            ops: vec![
                PackedEvalOp::AccInit(Operand::Source(value)),
                PackedEvalOp::CacheStore {
                    value,
                    from: CacheStoreFrom::Acc,
                },
                PackedEvalOp::BatchAccumulate {
                    coefficient_desc: None,
                    field: FieldKind::Base,
                },
                PackedEvalOp::AccInit(Operand::Resident(value)),
                PackedEvalOp::BatchAccumulate {
                    coefficient_desc: None,
                    field: FieldKind::Base,
                },
                PackedEvalOp::ReturnBatch { root },
            ],
            stats: PackedStats {
                unpacked_instructions: 5,
                packed_instructions: 5,
                arithmetic_instructions: 2,
                scalar_arithmetic_ops: 2,
                encoded_lanes: 10,
                ..PackedStats::default()
            },
        };
        let concrete = bind_backward_packed_plan(
            &packed,
            &layer,
            RootId(0),
            4,
            &BTreeMap::new(),
            &BwdSpecialTable::default(),
        )
        .unwrap();
        let instrs = &concrete.compiled.program.instrs;
        assert_eq!(instrs.len(), 4);
        assert!(matches!(
            &instrs[0],
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(_),
                ..
            }
        ));
        assert!(matches!(
            &instrs[1],
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                dst: Some(DstLine::Smem { .. }),
                src: None,
                ..
            }
        ));
        assert!(instrs[2..].iter().all(|instruction| {
            matches!(
                instruction,
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    dst: Some(dst),
                    src: None,
                    ..
                } if unpack_batch_dst(dst).is_some()
            )
        }));
    }

    #[test]
    fn batch_sink_preserves_acc_and_elides_logical_source_reload() {
        let source = OperandLine::LogicalGlobal { slot: 1, col: 2 };
        let sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(pack_batch_dst(BATCH_COEFFICIENT_ONE).unwrap()),
            src: None,
        };
        let load = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(source),
        };
        let mut program = Program {
            instrs: vec![load.clone(), sink.clone(), load.clone()],
        };

        elide_reloads_of_acc_preserved_by_batch_sink(&mut program, &BwdSpecialTable::default());

        assert_eq!(program.instrs, vec![load, sink]);
    }

    #[test]
    fn raw_source_batch_sink_is_hoisted_before_destructive_accumulator_use() {
        let source = OperandLine::LogicalGlobal { slot: 1, col: 2 };
        let challenge = OperandLine::Ldc {
            sub: LdcSub::ConstDerivedE4,
            idx: 0,
        };
        let source_load = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(source),
        };
        let raw_sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(pack_batch_dst(BATCH_COEFFICIENT_ONE).unwrap()),
            src: None,
        };
        let destructive_add = Instr::Add {
            field: OperandField::Ext,
            sign: Sign::Plus,
            promote: true,
            operands: vec![challenge],
        };
        let ext_sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext,
            dst: Some(pack_batch_dst(7).unwrap()),
            src: None,
        };
        let mut program = Program {
            instrs: vec![
                source_load.clone(),
                destructive_add.clone(),
                ext_sink.clone(),
                source_load.clone(),
                raw_sink.clone(),
            ],
        };

        hoist_raw_source_batch_sinks(&mut program);

        assert_eq!(
            program.instrs,
            vec![source_load, raw_sink, destructive_add, ext_sink,]
        );
    }

    #[test]
    fn raw_source_batch_sink_hoist_does_not_reconsider_inserted_sink() {
        let source = OperandLine::LogicalGlobal { slot: 1, col: 2 };
        let challenge = OperandLine::Ldc {
            sub: LdcSub::ConstDerivedE4,
            idx: 0,
        };
        let source_load = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(source),
        };
        let raw_sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(pack_batch_dst(BATCH_COEFFICIENT_ONE).unwrap()),
            src: None,
        };
        let destructive_add = Instr::Add {
            field: OperandField::Ext,
            sign: Sign::Plus,
            promote: true,
            operands: vec![challenge],
        };
        let ext_sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext,
            dst: Some(pack_batch_dst(7).unwrap()),
            src: None,
        };
        let mut program = Program {
            instrs: vec![
                source_load.clone(),
                destructive_add.clone(),
                ext_sink.clone(),
                source_load.clone(),
                destructive_add.clone(),
                ext_sink.clone(),
                source_load.clone(),
                raw_sink.clone(),
            ],
        };

        hoist_raw_source_batch_sinks(&mut program);

        assert_eq!(
            program.instrs,
            vec![
                source_load.clone(),
                destructive_add.clone(),
                ext_sink.clone(),
                source_load,
                raw_sink,
                destructive_add,
                ext_sink,
            ]
        );
    }

    #[test]
    fn raw_source_batch_sink_commutes_positive_add_to_initialize_from_source() {
        let source = OperandLine::LogicalGlobal { slot: 1, col: 2 };
        let challenge = OperandLine::Ldc {
            sub: LdcSub::ConstDerivedE4,
            idx: 0,
        };
        let challenge_load = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Ext,
            dst: None,
            src: Some(challenge),
        };
        let source_add = Instr::Add {
            field: OperandField::Base,
            sign: Sign::Plus,
            promote: false,
            operands: vec![source],
        };
        let ext_sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext,
            dst: Some(pack_batch_dst(7).unwrap()),
            src: None,
        };
        let source_load = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(source),
        };
        let raw_sink = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(pack_batch_dst(BATCH_COEFFICIENT_ONE).unwrap()),
            src: None,
        };
        let mut program = Program {
            instrs: vec![
                challenge_load.clone(),
                source_add,
                ext_sink.clone(),
                source_load.clone(),
                raw_sink.clone(),
            ],
        };

        hoist_raw_source_batch_sinks(&mut program);

        assert_eq!(
            program.instrs,
            vec![
                source_load,
                raw_sink,
                Instr::Add {
                    field: OperandField::Ext,
                    sign: Sign::Plus,
                    promote: true,
                    operands: vec![challenge],
                },
                ext_sink,
            ]
        );
    }

    #[test]
    fn direct_source_store_optimizer_does_not_rewrite_batch_sink() {
        let sink = pack_batch_dst(BATCH_COEFFICIENT_ONE).unwrap();
        let mut program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Ldc {
                        sub: LdcSub::Special,
                        idx: Special::One as u16,
                    }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(sink),
                    src: None,
                },
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Ldc {
                        sub: LdcSub::Special,
                        idx: Special::NegOne as u16,
                    }),
                },
            ],
        };
        let expected = program.clone();
        fold_direct_source_stores_with_mode(&mut program, true);
        assert_eq!(program, expected);
    }

    #[test]
    fn return_acc_binds_without_instruction() {
        let layer = return_acc_layer(false);
        let roots = [RootId(0)];
        let packed = return_acc_packed(&layer, &roots);
        let concrete = bind_packed_plan(&packed, &layer, &roots, 0, 4).unwrap();
        let resolvers = resolvers();

        assert!(matches!(
            concrete.terminal,
            ConcreteTerminal::ReturnAcc { .. }
        ));
        assert_eq!(
            concrete.compiled.program.instrs.len(),
            packed.stats.packed_instructions
        );
        assert_eq!(
            decode(&concrete.encoded).unwrap(),
            concrete.compiled.program
        );
        validate_concrete_eval_program(&concrete, &layer).unwrap();
        assert_eq!(
            interpret_program_row_acc(&concrete.compiled, &layer, &resolvers, 0).unwrap(),
            eval_layer_expr(&layer, layer.roots[0].expr, 0, &resolvers)
        );
        assert!(
            disassemble_concrete_eval_program("return", &concrete, Some(&layer))
                .contains("terminal = ReturnAcc")
        );
    }

    #[test]
    fn return_acc_rejects_duplicate_terminal() {
        let layer = return_acc_layer(false);
        let roots = [RootId(0)];
        let mut packed = return_acc_packed(&layer, &roots);
        let terminal = packed
            .ops
            .iter()
            .find(|op| matches!(op, PackedEvalOp::ReturnAcc { .. }))
            .unwrap()
            .clone();
        packed.ops.push(terminal);

        assert!(matches!(
            bind_packed_plan(&packed, &layer, &roots, 0, 4),
            Err(ConcreteBindError::DuplicateReturnAcc)
        ));
    }

    #[test]
    fn return_acc_rejects_mixed_commit() {
        let layer = return_acc_layer(true);
        let roots = [RootId(0), RootId(1)];
        let packed = return_acc_packed(&layer, &roots);

        assert!(matches!(
            bind_packed_plan(&packed, &layer, &roots, 0, 4),
            Err(ConcreteBindError::MixedForwardAndReturnTerminal)
        ));
    }

    #[test]
    fn return_acc_rejects_operations_after_terminal() {
        let layer = return_acc_layer(false);
        let roots = [RootId(0)];
        let mut packed = return_acc_packed(&layer, &roots);
        packed.ops.push(packed.ops[0].clone());

        assert!(matches!(
            bind_packed_plan(&packed, &layer, &roots, 0, 4),
            Err(ConcreteBindError::MixedForwardAndReturnTerminal)
        ));
    }

    #[test]
    fn return_acc_rejects_cache_location_metadata() {
        let layer = return_acc_layer(false);
        let roots = [RootId(0)];
        let packed = return_acc_packed(&layer, &roots);
        let mut concrete = bind_packed_plan(&packed, &layer, &roots, 0, 4).unwrap();
        concrete.compiled.ctx.cache_loc.insert(RootId(0), (0, 0));

        assert_eq!(
            validate_concrete_eval_program(&concrete, &layer),
            Err(ConcreteBindError::MixedForwardAndReturnTerminal)
        );
    }

    #[test]
    fn forward_validation_requires_all_materialized_outputs() {
        let mut layer = return_acc_layer(true);
        layer.roots.truncate(1);
        let roots = [RootId(0)];
        let packed = return_acc_packed(&layer, &roots);
        let mut actions = HashMap::new();
        actions.insert(RootId(0), ForwardAction::Compute);
        let mut concrete =
            bind_packed_plan_with_actions(&packed, &layer, &roots, 0, 4, &actions, &HashMap::new())
                .unwrap();
        validate_concrete_eval_program(&concrete, &layer).unwrap();
        concrete.compiled.root_outputs.clear();

        assert!(matches!(
            validate_concrete_eval_program(&concrete, &layer),
            Err(ConcreteBindError::RootCountMismatch { .. })
        ));
    }

    fn bind_single_forward_action(action: ForwardAction) -> (DagLayer, ConcreteEvalProgram) {
        let mut layer = return_acc_layer(true);
        layer.roots.truncate(1);
        let roots = if action == ForwardAction::Compute {
            vec![RootId(0)]
        } else {
            Vec::new()
        };
        let packed = return_acc_packed(&layer, &roots);
        let actions = HashMap::from([(RootId(0), action)]);
        let concrete =
            bind_packed_plan_with_actions(&packed, &layer, &roots, 0, 4, &actions, &HashMap::new())
                .unwrap();
        (layer, concrete)
    }

    #[test]
    fn forward_validation_accepts_compute_action() {
        let (layer, concrete) = bind_single_forward_action(ForwardAction::Compute);

        validate_concrete_eval_program(&concrete, &layer).unwrap();
        assert!(matches!(
            concrete.compiled.root_outputs.as_slice(),
            [(RootId(0), RootOutput::Cell(_))]
        ));
        assert!(concrete.compiled.skipped.is_empty());
    }

    #[test]
    fn forward_validation_accepts_copy_alias_action() {
        let (layer, concrete) = bind_single_forward_action(ForwardAction::CopyAlias {
            src_addr: GKRAddress::BaseLayerWitness(0),
            dst_addr: GKRAddress::BaseLayerWitness(1),
        });

        validate_concrete_eval_program(&concrete, &layer).unwrap();
        assert!(matches!(
            concrete.compiled.root_outputs.as_slice(),
            [(RootId(0), RootOutput::Alias(_))]
        ));
        assert!(concrete.compiled.skipped.is_empty());
    }

    #[test]
    fn forward_validation_accepts_skip_scratch_prefill_action() {
        let (layer, concrete) = bind_single_forward_action(ForwardAction::SkipScratchPrefill);

        validate_concrete_eval_program(&concrete, &layer).unwrap();
        assert!(concrete.compiled.root_outputs.is_empty());
        assert_eq!(concrete.compiled.skipped, vec![RootId(0)]);
    }

    #[test]
    fn forward_validation_rejects_duplicate_root_classification() {
        let (layer, mut concrete) = bind_single_forward_action(ForwardAction::SkipScratchPrefill);
        concrete.compiled.skipped.push(RootId(0));

        assert!(matches!(
            validate_concrete_eval_program(&concrete, &layer),
            Err(ConcreteBindError::RootCountMismatch { .. })
        ));
    }

    #[test]
    fn forward_validation_rejects_overlapping_root_categories() {
        let (layer, mut concrete) = bind_single_forward_action(ForwardAction::CopyAlias {
            src_addr: GKRAddress::BaseLayerWitness(0),
            dst_addr: GKRAddress::BaseLayerWitness(1),
        });
        concrete.compiled.skipped.push(RootId(0));

        assert!(matches!(
            validate_concrete_eval_program(&concrete, &layer),
            Err(ConcreteBindError::RootCountMismatch { .. })
        ));
    }

    fn assert_return_acc_rejects_forward_action(action: ForwardAction) {
        let layer = return_acc_layer(false);
        let roots = [RootId(0)];
        let packed = return_acc_packed(&layer, &roots);
        let mut concrete = bind_packed_plan(&packed, &layer, &roots, 0, 4).unwrap();
        concrete
            .compiled
            .ctx
            .actions
            .insert(RootId(0), action.clone());
        assert!(matches!(
            validate_concrete_eval_program(&concrete, &layer),
            Err(ConcreteBindError::MixedForwardAndReturnTerminal)
        ));

        let actions = HashMap::from([(RootId(0), action)]);
        assert!(matches!(
            bind_packed_plan_with_actions(&packed, &layer, &roots, 0, 4, &actions, &HashMap::new(),),
            Err(ConcreteBindError::MixedForwardAndReturnTerminal)
        ));
    }

    #[test]
    fn return_acc_rejects_compute_action() {
        assert_return_acc_rejects_forward_action(ForwardAction::Compute);
    }

    #[test]
    fn return_acc_rejects_copy_alias_action() {
        assert_return_acc_rejects_forward_action(ForwardAction::CopyAlias {
            src_addr: GKRAddress::BaseLayerWitness(0),
            dst_addr: GKRAddress::BaseLayerWitness(1),
        });
    }

    #[test]
    fn return_acc_rejects_skip_scratch_prefill_action() {
        assert_return_acc_rejects_forward_action(ForwardAction::SkipScratchPrefill);
    }

    #[test]
    fn concrete_store_reload_roundtrip_is_elided() {
        let store = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(DstLine::Smem { cell: 3 }),
            src: None,
        };
        let reload = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Smem { cell: 3 }),
        };
        let different_reload = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Smem { cell: 4 }),
        };
        let mut program = Program {
            instrs: vec![store.clone(), reload, different_reload.clone()],
        };

        elide_accumulator_cell_roundtrips(&mut program);

        assert_eq!(program.instrs, vec![store, different_reload]);
    }

    #[test]
    fn dead_accumulator_load_is_folded_into_direct_store() {
        let source = OperandLine::Ldc {
            sub: LdcSub::Const,
            idx: 7,
        };
        let overwrite = Instr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(OperandLine::Special { desc: 4 }),
        };
        let mut program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(source),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 3 }),
                    src: None,
                },
                overwrite.clone(),
            ],
        };

        fold_direct_source_stores(&mut program);

        assert_eq!(
            program.instrs,
            vec![
                Instr::Mov {
                    dir: MovDir::DstFromSrc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 3 }),
                    src: Some(source),
                },
                overwrite,
            ]
        );
    }

    #[test]
    fn direct_store_fold_requires_a_following_accumulator_overwrite() {
        let mut program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Smem { cell: 2 }),
                },
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 3 }),
                    src: None,
                },
                Instr::Add {
                    field: OperandField::Base,
                    sign: Sign::Plus,
                    promote: false,
                    operands: vec![OperandLine::Smem { cell: 4 }],
                },
            ],
        };
        let original = program.clone();

        fold_direct_source_stores(&mut program);

        assert_eq!(program, original);
    }

    #[test]
    fn load_mul_add_is_folded_to_canonical_signed_fma() {
        let loaded = OperandLine::Ldc {
            sub: LdcSub::ConstDerivedE4,
            idx: 2,
        };
        let factor = OperandLine::Smem { cell: 3 };
        let addend = OperandLine::Smem { cell: 4 };
        let mut program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Ext,
                    dst: None,
                    src: Some(loaded),
                },
                Instr::Mul {
                    field: OperandField::Base,
                    promote: false,
                    negate_acc: true,
                    operands: vec![factor],
                },
                Instr::Add {
                    field: OperandField::Ext,
                    sign: Sign::Plus,
                    promote: false,
                    operands: vec![addend],
                },
            ],
        };

        fold_load_mul_add(&mut program);

        assert_eq!(
            program.instrs,
            vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Ext,
                    dst: None,
                    src: Some(addend),
                },
                Instr::Fma {
                    field_lhs: OperandField::Base,
                    field_rhs: OperandField::Ext,
                    sign: Sign::Minus,
                    promote: false,
                    pairs: vec![(factor, loaded)],
                },
            ]
        );
    }

    #[test]
    fn load_mul_add_fold_rejects_subtraction() {
        let mut program = Program {
            instrs: vec![
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Smem { cell: 2 }),
                },
                Instr::Mul {
                    field: OperandField::Base,
                    promote: false,
                    negate_acc: false,
                    operands: vec![OperandLine::Smem { cell: 3 }],
                },
                Instr::Add {
                    field: OperandField::Base,
                    sign: Sign::Minus,
                    promote: false,
                    operands: vec![OperandLine::Smem { cell: 4 }],
                },
            ],
        };
        let original = program.clone();

        fold_load_mul_add(&mut program);

        assert_eq!(program, original);
    }

    #[test]
    fn fma_fold_removes_now_dead_partial_store() {
        let total = DstLine::Smem { cell: 0 };
        let source = OperandLine::Smem { cell: 8 };
        let coefficient = OperandLine::Special { desc: 3 };
        let final_store = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext,
            dst: Some(total),
            src: None,
        };
        let mut program = Program {
            instrs: vec![
                final_store.clone(),
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(source),
                },
                Instr::Mul {
                    field: OperandField::Ext,
                    promote: true,
                    negate_acc: false,
                    operands: vec![coefficient],
                },
                Instr::Add {
                    field: OperandField::Ext,
                    sign: Sign::Plus,
                    promote: false,
                    operands: vec![OperandLine::Smem { cell: 0 }],
                },
                final_store.clone(),
            ],
        };

        fold_load_mul_add(&mut program);
        elide_accumulator_cell_roundtrips(&mut program);

        assert_eq!(
            program.instrs,
            vec![
                Instr::Fma {
                    field_lhs: OperandField::Base,
                    field_rhs: OperandField::Ext,
                    sign: Sign::Plus,
                    promote: false,
                    pairs: vec![(source, coefficient)],
                },
                final_store,
            ]
        );
    }

    #[test]
    fn fma_fold_keeps_partial_store_read_through_overlapping_base_cell() {
        let total = DstLine::Smem { cell: 0 };
        let store = Instr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Ext,
            dst: Some(total),
            src: None,
        };
        let fma = Instr::Fma {
            field_lhs: OperandField::Base,
            field_rhs: OperandField::Ext,
            sign: Sign::Plus,
            promote: false,
            pairs: vec![(
                OperandLine::Smem { cell: 1 },
                OperandLine::Special { desc: 3 },
            )],
        };
        let mut program = Program {
            instrs: vec![store.clone(), fma.clone(), store.clone()],
        };

        elide_accumulator_cell_roundtrips(&mut program);

        assert_eq!(program.instrs, vec![store.clone(), fma, store]);
    }

    #[test]
    fn metadata_drop_does_not_extend_physical_lifetime() {
        let value = ValueRef {
            expr: ExprId(0),
            fingerprint: ValueFingerprint([1, 0]),
            field: FieldKind::Base,
        };
        let plan = PackedEvalPlan {
            ops: vec![
                PackedEvalOp::CacheStore {
                    value,
                    from: CacheStoreFrom::Source,
                },
                PackedEvalOp::AccInit(Operand::Resident(value)),
                PackedEvalOp::CacheDrop(value),
            ],
            stats: PackedStats::default(),
        };

        let lifetimes =
            analyze_lifetimes(&plan, ConcreteSourceMode::Forward).expect("valid resident lifetime");
        assert_eq!(lifetimes.intervals.len(), 1);
        assert_eq!(lifetimes.intervals[0].start, 0);
        assert_eq!(lifetimes.intervals[0].end, 2);
    }

    fn reference_base_search(
        remaining: &mut Vec<Interval>,
        ext_by_quad: &[Vec<Interval>],
        bases_by_lane: &mut Vec<Vec<Interval>>,
    ) -> bool {
        if remaining.is_empty() {
            return true;
        }
        let mut choice = None::<(
            usize,
            Vec<usize>,
            (usize, std::cmp::Reverse<usize>, StorageId),
        )>;
        for (index, &interval) in remaining.iter().enumerate() {
            let lanes = (0..bases_by_lane.len())
                .filter(|&lane| base_fits_lane(interval, lane, ext_by_quad, bases_by_lane))
                .collect::<Vec<_>>();
            if lanes.is_empty() {
                return false;
            }
            let key = (
                lanes.len(),
                std::cmp::Reverse(interval.end - interval.start),
                interval.id,
            );
            if choice
                .as_ref()
                .is_none_or(|(_, _, best_key)| key < *best_key)
            {
                choice = Some((index, lanes, key));
            }
        }
        let (index, mut lanes, _) = choice.expect("non-empty reference search has a choice");
        let interval = remaining.swap_remove(index);
        let mut signatures = HashSet::<(Vec<StorageId>, Vec<StorageId>)>::new();
        lanes.retain(|&lane| {
            signatures.insert((
                ext_by_quad
                    .get(lane / 4)
                    .into_iter()
                    .flatten()
                    .map(|other| other.id)
                    .collect(),
                bases_by_lane[lane].iter().map(|other| other.id).collect(),
            ))
        });
        for lane in lanes {
            bases_by_lane[lane].push(interval);
            if reference_base_search(remaining, ext_by_quad, bases_by_lane) {
                return true;
            }
            bases_by_lane[lane].pop();
        }
        remaining.push(interval);
        false
    }

    fn assert_valid_base_locations(
        bases: &[Interval],
        ext_by_quad: &[Vec<Interval>],
        budget: usize,
        locations: &HashMap<StorageId, u16>,
    ) {
        assert_eq!(locations.len(), bases.len());
        for (index, &interval) in bases.iter().enumerate() {
            let lane = locations[&interval.id] as usize;
            assert!(lane < budget);
            assert!(
                ext_by_quad
                    .get(lane / 4)
                    .into_iter()
                    .flatten()
                    .all(|other| !overlap(interval, *other))
            );
            for &other in &bases[index + 1..] {
                if locations[&other.id] as usize == lane {
                    assert!(!overlap(interval, other));
                }
            }
        }
    }

    #[test]
    fn scalar_peak_does_not_certify_aligned_fixed_cell_placement() {
        let interval = |id, field, start, end| Interval {
            id: StorageId(id),
            field,
            start,
            end,
        };
        let intervals = vec![
            interval(0, FieldKind::Ext, 0, 78),
            interval(1, FieldKind::Base, 40, 323),
            interval(2, FieldKind::Base, 50, 95),
            interval(3, FieldKind::Base, 60, 119),
            interval(4, FieldKind::Ext, 66, 74),
            interval(5, FieldKind::Base, 70, 99),
            interval(6, FieldKind::Base, 84, 125),
            interval(7, FieldKind::Ext, 114, 142),
            interval(8, FieldKind::Ext, 122, 132),
        ];

        assert_eq!(peak_live_lanes(&intervals), 12);
        // Neither the fast fixed two-pass allocator nor its bounded exact
        // fallback can seat the witness at b12.
        assert!(place_intervals(&intervals, 12, PlacementMode::GreedyOnly).is_err());
        assert!(place_intervals(&intervals, 12, PlacementMode::Exact).is_err());
        // With one additional lane the same fixed two-pass strategy succeeds,
        // so no relocation is introduced when it is unnecessary.
        assert!(place_intervals(&intervals, 13, PlacementMode::Exact).is_ok());
        let relocated = place_intervals_with_relocation(&intervals, 12)
            .expect("one BF relocation seats the width-feasible plan");
        assert_eq!(relocated.definition_locations.len(), intervals.len());
        assert_eq!(relocated.move_count(), 1);
    }

    #[test]
    fn exact_base_bitsets_recover_from_a_greedy_list_coloring_trap() {
        let base = |id, start, end| Interval {
            id: StorageId(id),
            field: FieldKind::Base,
            start,
            end,
        };
        let bases = vec![
            base(0, 0, 2),
            base(1, 1, 5),
            base(2, 1, 5),
            base(3, 1, 5),
            base(4, 1, 5),
        ];
        // The later E4 reservation makes the four long BF intervals eligible
        // only for lanes 0..4. Greedy puts the short, unconstrained interval in
        // lane 0 first and gets stuck; exact placement must put it in lane 4.
        let ext_by_quad = vec![
            Vec::new(),
            vec![Interval {
                id: StorageId(5),
                field: FieldKind::Ext,
                start: 3,
                end: 5,
            }],
        ];
        assert!(pack_base_intervals_greedy(&bases, &ext_by_quad, 8).is_none());

        let conflicts = BaseConflictGraph::new(&bases);
        let mut nodes = 1_000_000;
        let locations =
            pack_base_intervals_bounded(&bases, &conflicts, &ext_by_quad, 8, &mut nodes)
                .expect("exact BF placement recovers from the greedy lane choice");
        assert!(locations[&StorageId(0)] >= 4);
        assert!(
            (1..=4).all(|id| locations[&StorageId(id)] < 4),
            "the four E4-constrained BF intervals occupy the first quad"
        );
    }

    #[test]
    fn exact_base_bitsets_match_vector_reference_on_small_instances() {
        let mut state = 0x6a09_e667_f3bc_c909u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        for case in 0..128u32 {
            let count = 5 + next() as usize % 4;
            let mut bases = (0..count)
                .map(|index| {
                    let start = next() as usize % 12;
                    Interval {
                        id: StorageId(index as u32),
                        field: FieldKind::Base,
                        start,
                        end: start + next() as usize % 6,
                    }
                })
                .collect::<Vec<_>>();
            bases.sort_by_key(|interval| (interval.start, interval.id));
            let ext_by_quad = (0..2)
                .map(|quad| {
                    let start = next() as usize % 12;
                    (next() % 3 != 0)
                        .then_some(Interval {
                            id: StorageId(100 + quad),
                            field: FieldKind::Ext,
                            start,
                            end: start + next() as usize % 5,
                        })
                        .into_iter()
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            let mut reference_remaining = bases.clone();
            let reference = reference_base_search(
                &mut reference_remaining,
                &ext_by_quad,
                &mut vec![Vec::new(); 8],
            );
            let conflicts = BaseConflictGraph::new(&bases);
            let mut nodes = 1_000_000;
            let bitset =
                pack_base_intervals_bounded(&bases, &conflicts, &ext_by_quad, 8, &mut nodes);
            assert_eq!(
                bitset.is_some(),
                reference,
                "BF exact placement disagreement in generated case {case}"
            );
            if let Some(locations) = bitset {
                assert_valid_base_locations(&bases, &ext_by_quad, 8, &locations);
            }
        }
    }
}
