//! Lowers a backward program and round binding to the CUDA descriptor.

use gpu_gkr_compiler::{
    category_arity, decode_continuation_program, decode_r0_program, split_round_robin,
    CoefficientRecipeId, ImmediateId, LeanAtom, LeanCodecError, LeanProgram, LeanSourceBinding,
    LeanTerm, TermCategory, LEAN_CONT_OPCODES, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES,
    LEAN_R0_OPCODES, LEAN_WORDS_PER_TERM, SOURCE_NONE, SOURCE_WINDOW_COLUMNS,
};
use gpu_gkr_compiler::{ContinuationLayerProgram, R0LayerProgram};

use super::seg_desc::{
    bwd_seg_lane, bwd_seg_lane_slot, BwdSegAddrSlot, BwdSegDesc, BwdSegSourceRecord,
    BWD_COEFF_MAX_FOLD_DEPTH, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
    BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_SEG_ADDR_NONE, BWD_SEG_ADDR_SLOTS, BWD_SEG_CONST_BANK,
    BWD_SEG_C_INIT_NONE, BWD_SEG_MAX_K, BWD_SEG_MAX_SOURCES,
};
use crate::backward::GkrEqSizes;
use crate::forward::vm::lower::ResolvedColumn;
use crate::upstream::{BwdRegime, PrimeField};
use gpu_core::primitives::field::{BF, E4};

const BF_COLUMN_BYTES: u32 = 4;
const E4_COLUMN_BYTES: u32 = 16;

pub(super) fn bwd_coeff_fold_depth(round: u8) -> u8 {
    match round {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        _ => 1,
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct ResolvedAddrSlot {
    pub base: Option<ResolvedColumn>,
    pub procedural_kind: Option<u8>,
    pub read_elements: u32,
    pub columns: usize,
    /// `base.ptr` is an allocation-relative byte offset until launch.
    pub deferred_base: bool,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct ResolvedSourceAddr {
    pub read_slot: usize,
    pub read_column: usize,
    pub publish: Option<(usize, usize)>,
    pub backing_depth: u8,
}

// ── Source classes ───────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(super) enum SourceClass {
    BfDirect = 0,
    BfInlineD1 = 1,
    BfInlineD2 = 2,
    E4Direct = 3,
    ProceduralInline = 4,
}

impl SourceClass {
    pub(super) const fn code(self) -> u8 {
        self as u8
    }
}

const _: () = {
    assert!(SourceClass::BfDirect.code() == 0);
    assert!(SourceClass::BfInlineD1.code() == 1);
    assert!(SourceClass::BfInlineD2.code() == 2);
    assert!(SourceClass::E4Direct.code() == 3);
    assert!(SourceClass::ProceduralInline.code() == 4);
    assert!(BWD_COEFF_PUBLISH_TARGET_DEPTH == 3);
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SourceOrigin {
    Bf,
    E4,
    Procedural,
}

// ── Per-list work model ──────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AnnotatedTerm {
    pub category: TermCategory,
    pub operands: [Option<SourceClass>; 2],
}

// Relative instruction costs used only to balance lists.
fn static_term_work(term: &AnnotatedTerm) -> u64 {
    static_term_work_base(term.category) + operand_work(term)
}

fn static_term_work_base(category: TermCategory) -> u64 {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => 2,
        TermCategory::C2ProductBfBf | TermCategory::C2ProductBfE4 | TermCategory::C2ProductE4E4 => {
            6
        }
        TermCategory::DualProductE4 => 10,
    }
}

fn operand_work(term: &AnnotatedTerm) -> u64 {
    term.operands
        .iter()
        .flatten()
        .map(|class| match class {
            SourceClass::BfInlineD1 => 4,
            SourceClass::BfInlineD2 => 10,
            SourceClass::ProceduralInline => 3,
            SourceClass::BfDirect | SourceClass::E4Direct => 0,
        })
        .sum()
}

// ── Atoms: the unit the deal places ──────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SegMember {
    pub annotated: AnnotatedTerm,
    pub immediate: u16,
}

impl SegMember {
    fn immediate_sides(&self) -> Option<u64> {
        if self.immediate < ImmediateId::RESERVED {
            return None;
        }
        Some(match self.annotated.category {
            TermCategory::DualProductE4
            | TermCategory::C2ProductBfBf
            | TermCategory::C2ProductBfE4
            | TermCategory::C2ProductE4E4 => 2,
            TermCategory::C0LinearBf | TermCategory::C0LinearE4 => 1,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SegAtom {
    Term(AnnotatedTerm),
    Group {
        core: u16,
        has_c0: bool,
        has_c2: bool,
        members: Vec<SegMember>,
    },
}

fn member_work(member: &SegMember) -> u64 {
    let body = match member.annotated.category {
        TermCategory::C0LinearE4 => 1,
        TermCategory::DualProductE4 => 8,
        other => static_term_work_base(other),
    };
    let imm_surcharge = member.immediate_sides().unwrap_or(0);
    body + operand_work(&member.annotated) + imm_surcharge
}

fn atom_work(atom: &SegAtom) -> u64 {
    match atom {
        SegAtom::Term(term) => static_term_work(term),
        SegAtom::Group {
            members,
            has_c0,
            has_c2,
            ..
        } => {
            let base: u64 = members.iter().map(member_work).sum();
            base + 2 * (u64::from(*has_c0) + u64::from(*has_c2))
        }
    }
}

fn deal_atoms(costs: &[u64], k: usize) -> Vec<Vec<usize>> {
    let mut lists = vec![Vec::new(); k];
    let mut load = vec![0u64; k];
    for (atom, &cost) in costs.iter().enumerate() {
        let target = (0..k)
            .min_by_key(|&list| (load[list], list))
            .expect("k lists");
        lists[target].push(atom);
        load[target] += cost.max(1);
    }
    lists
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SegUnitEmit {
    Atom {
        first: usize,
        span: usize,
    },
    GroupChunk {
        header: usize,
        first_member: usize,
        members: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SegDealUnit {
    pub cost: u64,
    pub emit: SegUnitEmit,
}

const SEG_CHOP_DIVISOR: u64 = 4;

// Split expensive groups without exceeding descriptor capacity. Chunks remain
// adjacent and each repays the shared core multiplication.
fn chop_atoms(
    seg_atoms: &[SegAtom],
    atom_spans: &[(usize, usize)],
    k: usize,
    record_capacity: usize,
) -> Vec<SegDealUnit> {
    let total: u64 = seg_atoms.iter().map(atom_work).sum();
    let threshold = (total / (SEG_CHOP_DIVISOR * k as u64)).max(1);
    let records = atom_spans
        .last()
        .map(|&(first, span)| first + span)
        .unwrap_or(0);
    let mut budget = record_capacity.saturating_sub(records) as u64;
    let mut units = Vec::with_capacity(seg_atoms.len());
    for (atom, &(first, span)) in seg_atoms.iter().zip(atom_spans) {
        let cost = atom_work(atom);
        let whole = SegDealUnit {
            cost,
            emit: SegUnitEmit::Atom { first, span },
        };
        let SegAtom::Group {
            has_c0,
            has_c2,
            members,
            ..
        } = atom
        else {
            units.push(whole);
            continue;
        };
        let core_work = 2 * (u64::from(*has_c0) + u64::from(*has_c2));
        let member_total: u64 = members.iter().map(member_work).sum();
        let chunks = if cost > threshold {
            cost.div_ceil(threshold)
                .min(members.len() as u64)
                .min((member_total / (2 * core_work).max(1)).max(1))
                .min(1 + budget)
        } else {
            1
        };
        if chunks <= 1 {
            units.push(whole);
            continue;
        }
        budget -= chunks - 1;
        let chunks = chunks as usize;
        let base = members.len() / chunks;
        let extra = members.len() % chunks;
        let mut member = 0usize;
        for chunk in 0..chunks {
            let count = base + usize::from(chunk < extra);
            let cost: u64 = members[member..member + count]
                .iter()
                .map(member_work)
                .sum::<u64>()
                + core_work;
            units.push(SegDealUnit {
                cost,
                emit: SegUnitEmit::GroupChunk {
                    header: first,
                    first_member: first + 1 + member,
                    members: count,
                },
            });
            member += count;
        }
        debug_assert_eq!(member, members.len(), "every member lands in one chunk");
    }
    units
}

// ── Round binding and setup ──────────────────────────────────────────────────

pub(super) struct BwdSegRoundBinding<'a> {
    pub round: u32,
    pub rows: usize,
    pub slots: &'a [ResolvedAddrSlot],
    pub sources: &'a [ResolvedSourceAddr],
    pub claim_point_len: usize,
    pub coefficient_count: usize,
    pub c_init: Option<CoefficientRecipeId>,
    pub immediates: &'a [u32],
    pub eq_low: *const E4,
    pub eq_sizes: GkrEqSizes,
    pub contributions: *mut E4,
    pub acc_size: u32,
}

pub(super) type BwdSegSetup = Box<BwdSegDesc>;

// ── Errors ───────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BwdSegLowerError {
    InvalidListCount {
        k: usize,
    },
    RoundTooDeep {
        round: u32,
    },
    R0RoundMismatch {
        round: u32,
    },
    R0CarriesCInit {
        id: CoefficientRecipeId,
    },
    InvalidCInit {
        index: u32,
    },
    ProgramOverflow {
        words: usize,
        cap: usize,
    },
    Codec(LeanCodecError),
    SourceWindowOverflow {
        windows: usize,
        cap: usize,
    },
    SourceWindowCountMismatch {
        compiled: usize,
        bound: usize,
    },
    WindowColumnOverflow {
        window: u8,
        offset: usize,
    },
    UnknownProceduralKind {
        window: u8,
        kind: u8,
    },
    MultiColumnProceduralWindow {
        window: u8,
        columns: usize,
    },
    MissingReadBacking {
        window: u8,
    },
    ProceduralWindowWithMatrixRead {
        window: u8,
    },
    NullWindowGeometry {
        window: u8,
    },
    StrideNotPowerOfTwo {
        window: u8,
        stride_bytes: u32,
    },
    WindowStrideMismatch {
        window: u8,
        is_e4: bool,
        stride_bytes: u32,
    },
    InvalidDepths {
        window: u8,
        backing_depth: u8,
        target_depth: u8,
    },
    UnsupportedFoldDelta {
        window: u8,
        delta: u8,
        fold_depth: u8,
    },
    UnexpectedPublishBacking {
        window: u8,
    },
    ExplicitPublishGeometry {
        window: u8,
        is_e4: bool,
        stride_bytes: u32,
    },
    ReadSpanOverflow {
        window: u8,
        needed: u32,
        have: u32,
    },
    MissingPublishBacking {
        window: u8,
    },
    BaseReadAtFoldedDepth {
        window: u8,
        backing_depth: u8,
    },
    UnsafePublishAlias {
        window: u8,
        other: u8,
    },
    SourceOverflow {
        sources: usize,
        cap: usize,
    },
    SourceWindowOutOfRange {
        source: usize,
        window: u8,
    },
    SourceColumnOutOfWindow {
        source: usize,
        window: u8,
        column: u16,
    },
    SourceSlotOutOfRange {
        term: usize,
        slot: u16,
    },
    CoefficientIndexPastBank {
        index: usize,
        entries: usize,
    },
    CoefficientBankOverflow {
        coefficients: usize,
        cap: usize,
    },
    ImmediateTableOverflow {
        len: usize,
    },
    ImmediateOutOfRange {
        record: usize,
        id: u16,
    },
    ClaimPointTooShort {
        round: u8,
        entries: usize,
    },
    RowsOutOfRange {
        rows: usize,
    },
    AccSizeRowsMismatch {
        rows: usize,
        acc_size: u32,
    },
    NullRuntimePointer {
        what: &'static str,
    },
}

impl From<LeanCodecError> for BwdSegLowerError {
    fn from(error: LeanCodecError) -> Self {
        BwdSegLowerError::Codec(error)
    }
}

// ── The assignment matrix ────────────────────────────────────────────────────

fn assign_class(origin: SourceOrigin, delta: u8) -> (SourceClass, bool) {
    match (origin, delta) {
        (SourceOrigin::Procedural, delta) if delta < BWD_COEFF_PUBLISH_TARGET_DEPTH => {
            (SourceClass::ProceduralInline, false)
        }
        (SourceOrigin::Procedural, _) => (SourceClass::E4Direct, true),
        (SourceOrigin::Bf, 0) => (SourceClass::BfDirect, false),
        (SourceOrigin::Bf, 1) => (SourceClass::BfInlineD1, false),
        (SourceOrigin::Bf, 2) => (SourceClass::BfInlineD2, false),
        (SourceOrigin::Bf, _) => (SourceClass::E4Direct, true),
        (SourceOrigin::E4, 0) => (SourceClass::E4Direct, false),
        (SourceOrigin::E4, _) => (SourceClass::E4Direct, true),
    }
}

pub(super) fn materializes(origin: SourceOrigin, delta: u8) -> bool {
    assign_class(origin, delta).1
}

// ── Lowering ─────────────────────────────────────────────────────────────────

/// A zero-initialized `Box<T>`.
///
/// # Safety
///
/// The all-zero bit pattern must be a valid `T`.
pub(crate) unsafe fn zeroed_box<T>() -> Box<T> {
    let layout = std::alloc::Layout::new::<T>();
    let ptr = std::alloc::alloc_zeroed(layout) as *mut T;
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    Box::from_raw(ptr)
}

struct LoweredSource {
    record: BwdSegSourceRecord,
    class: SourceClass,
    publishes: bool,
}

struct SegProgramRef<'a> {
    regime: BwdRegime,
    program: &'a LeanProgram,
    binding: &'a LeanSourceBinding,
}

fn lower_bwd_seg_view(
    artifact: SegProgramRef<'_>,
    binding: &BwdSegRoundBinding<'_>,
    k: usize,
) -> Result<BwdSegSetup, BwdSegLowerError> {
    if k == 0 || k > BWD_SEG_MAX_K {
        return Err(BwdSegLowerError::InvalidListCount { k });
    }
    let round = u8::try_from(binding.round).map_err(|_| BwdSegLowerError::RoundTooDeep {
        round: binding.round,
    })?;
    let regime = artifact.regime;
    if regime == BwdRegime::R0 && round != 0 {
        return Err(BwdSegLowerError::R0RoundMismatch {
            round: binding.round,
        });
    }
    let fold_depth = bwd_coeff_fold_depth(round);

    let coefficient_count = CoefficientRecipeId::RESERVED as usize + binding.coefficient_count;
    if coefficient_count > BWD_SEG_CONST_BANK {
        return Err(BwdSegLowerError::CoefficientBankOverflow {
            coefficients: coefficient_count,
            cap: BWD_SEG_CONST_BANK,
        });
    }

    let c_init_coeff = match binding.c_init {
        None => BWD_SEG_C_INIT_NONE,
        Some(id) if regime == BwdRegime::R0 => return Err(BwdSegLowerError::R0CarriesCInit { id }),
        Some(id) => {
            let index = usize::try_from(id.0).ok();
            index
                .filter(|index| *index < coefficient_count)
                .ok_or(BwdSegLowerError::InvalidCInit { index: id.0 })?;
            id.0
        }
    };

    let bound_by = 2 * (1usize << BWD_COEFF_MAX_FOLD_DEPTH).max(E4_COLUMN_BYTES as usize);
    if binding.rows == 0
        || binding
            .rows
            .checked_mul(bound_by)
            .and_then(|value| u32::try_from(value).ok())
            .is_none()
    {
        return Err(BwdSegLowerError::RowsOutOfRange { rows: binding.rows });
    }
    let logical_rows = binding.rows as u32;
    if binding.acc_size != logical_rows {
        return Err(BwdSegLowerError::AccSizeRowsMismatch {
            rows: binding.rows,
            acc_size: binding.acc_size,
        });
    }
    if binding.claim_point_len < usize::from(round) {
        return Err(BwdSegLowerError::ClaimPointTooShort {
            round,
            entries: binding.claim_point_len,
        });
    }
    if binding.eq_low.is_null() {
        return Err(BwdSegLowerError::NullRuntimePointer { what: "eq_low" });
    }
    if binding.contributions.is_null() {
        return Err(BwdSegLowerError::NullRuntimePointer {
            what: "contributions",
        });
    }

    // ── The wire ─────────────────────────────────────────────────────────────
    let atoms = match regime {
        BwdRegime::R0 => decode_r0_program(artifact.program)?,
        BwdRegime::Ext => decode_continuation_program(artifact.program)?,
    };
    let mut atom_spans = Vec::with_capacity(atoms.len());
    let mut record_count = 0usize;
    for atom in &atoms {
        let span = match atom {
            LeanAtom::Term(_) => 1,
            LeanAtom::Group { members, .. } => 1 + members.len(),
        };
        atom_spans.push((record_count, span));
        record_count += span;
    }
    debug_assert!(regime != BwdRegime::R0 || record_count == atoms.len());
    let words = artifact.program.words.len();
    if words > LEAN_DESCRIPTOR_PROGRAM_WORDS {
        return Err(BwdSegLowerError::ProgramOverflow {
            words,
            cap: LEAN_DESCRIPTOR_PROGRAM_WORDS,
        });
    }

    // ── The address table ────────────────────────────────────────────────────
    if binding.slots.len() > BWD_SEG_ADDR_SLOTS {
        return Err(BwdSegLowerError::SourceWindowOverflow {
            windows: binding.slots.len(),
            cap: BWD_SEG_ADDR_SLOTS,
        });
    }
    if binding.sources.len() != artifact.binding.source_count {
        return Err(BwdSegLowerError::SourceWindowCountMismatch {
            compiled: artifact.binding.source_count,
            bound: binding.sources.len(),
        });
    }
    let columns: Vec<usize> = binding.slots.iter().map(|slot| slot.columns).collect();
    for (index, count) in columns.iter().enumerate() {
        if *count == 0 || *count > SOURCE_WINDOW_COLUMNS {
            return Err(BwdSegLowerError::WindowColumnOverflow {
                window: index as u8,
                offset: *count,
            });
        }
    }

    let mut table = Vec::with_capacity(binding.slots.len());
    for (index, slot) in binding.slots.iter().enumerate() {
        table.push(lower_slot(index as u8, slot)?);
    }

    // ── Sources ──────────────────────────────────────────────────────────────
    if binding.sources.len() > BWD_SEG_MAX_SOURCES {
        return Err(BwdSegLowerError::SourceOverflow {
            sources: binding.sources.len(),
            cap: BWD_SEG_MAX_SOURCES,
        });
    }
    let slot_columns = columns;
    let mut sources = Vec::with_capacity(binding.sources.len());
    let mut source_classes = Vec::with_capacity(binding.sources.len());
    let mut publishing = Vec::with_capacity(binding.sources.len());
    for (source, addr) in binding.sources.iter().enumerate() {
        let lowered = lower_source(source, addr, binding, &slot_columns, round, fold_depth)?;
        sources.push(lowered.record);
        source_classes.push(lowered.class);
        publishing.push(lowered.publishes);
    }
    let mut slot_read_extent = vec![0usize; table.len()];
    let mut slot_publishes = vec![false; table.len()];
    for record in &sources {
        let read_slot = bwd_seg_lane_slot(record.src);
        let width = if table[read_slot].origin == BWD_COEFF_ORIGIN_READ_EXT {
            E4_COLUMN_BYTES
        } else {
            BF_COLUMN_BYTES
        } as usize;
        let extent = 2 * binding.rows * (1usize << record.delta) * width;
        slot_read_extent[read_slot] = slot_read_extent[read_slot].max(extent);
        if record.cache != BWD_SEG_ADDR_NONE {
            slot_publishes[bwd_seg_lane_slot(record.cache)] = true;
        }
    }
    check_alias(
        &table,
        &slot_columns,
        &slot_read_extent,
        &slot_publishes,
        binding.rows,
    )?;

    // ── The wire, validated and annotated against those sources ──────────────
    let seg_atoms = annotate_atoms(
        &atoms,
        regime,
        &source_classes,
        coefficient_count,
        binding.immediates.len(),
    )?;
    let mut terms: Vec<(&LeanTerm, AnnotatedTerm)> =
        Vec::with_capacity(artifact.program.words.len() / LEAN_WORDS_PER_TERM);
    for (atom, annotated) in atoms.iter().zip(&seg_atoms) {
        match (atom, annotated) {
            (LeanAtom::Term(record), SegAtom::Term(term)) => terms.push((record, *term)),
            (
                LeanAtom::Group { members, .. },
                SegAtom::Group {
                    members: annotated, ..
                },
            ) => terms.extend(
                members
                    .iter()
                    .zip(annotated)
                    .map(|(record, member)| (record, member.annotated)),
            ),
            _ => unreachable!("the annotated atom shape follows the decoded one"),
        }
    }

    // ── Fold list ────────────────────────────────────────────────────────────
    // The sources the eval loop touches EARLIEST are folded LAST, so they are the
    // warmest in L1 when eval starts. First touch is taken over the COMMITTED
    // order, which is the global order the `K` warps advance through together.
    let mut first_touch = vec![usize::MAX; sources.len()];
    for (position, (term, _)) in terms.iter().enumerate() {
        for slot in [term.source_a, term.source_b] {
            if slot == SOURCE_NONE {
                continue;
            }
            let entry = &mut first_touch[usize::from(slot)];
            *entry = (*entry).min(position);
        }
    }
    let mut fold_source: Vec<u16> = (0..sources.len())
        .filter(|&source| publishing[source])
        .map(|source| source as u16)
        .collect();
    fold_source
        .sort_by_key(|&source| (std::cmp::Reverse(first_touch[usize::from(source)]), source));
    let num_foldable = fold_source.len() as u16;

    // ── The K-split ──────────────────────────────────────────────────────────
    let units: Vec<SegDealUnit> = if regime == BwdRegime::R0 {
        seg_atoms
            .iter()
            .zip(&atom_spans)
            .map(|(atom, &(first, span))| SegDealUnit {
                cost: atom_work(atom),
                emit: SegUnitEmit::Atom { first, span },
            })
            .collect()
    } else {
        chop_atoms(
            &seg_atoms,
            &atom_spans,
            k,
            LEAN_DESCRIPTOR_PROGRAM_WORDS / LEAN_WORDS_PER_TERM,
        )
    };
    let costs: Vec<u64> = units.iter().map(|unit| unit.cost).collect();
    let lists = if regime == BwdRegime::R0 {
        let positions: Vec<usize> = (0..units.len()).collect();
        split_round_robin(&positions, k)
    } else {
        deal_atoms(&costs, k)
    };
    let mut stream: Vec<u16> = Vec::with_capacity(artifact.program.words.len());
    let mut list_offset = vec![0u16; k + 1];
    for (list, list_units) in lists.iter().enumerate() {
        list_offset[list] = stream.len() as u16;
        for &unit in list_units {
            match units[unit].emit {
                SegUnitEmit::Atom { first, span } => {
                    let at = first * LEAN_WORDS_PER_TERM;
                    stream.extend_from_slice(
                        &artifact.program.words[at..at + span * LEAN_WORDS_PER_TERM],
                    );
                }
                SegUnitEmit::GroupChunk {
                    header,
                    first_member,
                    members,
                } => {
                    let at = header * LEAN_WORDS_PER_TERM;
                    stream.push(artifact.program.words[at]);
                    stream.push(members as u16);
                    stream.push(artifact.program.words[at + 2]);
                    let at = first_member * LEAN_WORDS_PER_TERM;
                    stream.extend_from_slice(
                        &artifact.program.words[at..at + members * LEAN_WORDS_PER_TERM],
                    );
                }
            }
        }
    }
    list_offset[k] = stream.len() as u16;
    if stream.len() > LEAN_DESCRIPTOR_PROGRAM_WORDS {
        return Err(BwdSegLowerError::ProgramOverflow {
            words: stream.len(),
            cap: LEAN_DESCRIPTOR_PROGRAM_WORDS,
        });
    }
    let immediates: Vec<u32> = binding
        .immediates
        .iter()
        .map(|&value| BF::from_u32_with_reduction(value).as_u32_raw_repr_reduced())
        .collect();

    // ── The descriptor ───────────────────────────────────────────────────────
    // SAFETY: `BwdSegDesc` is plain `repr(C)` data, so zero is valid for every
    // field and initializes its padding deterministically.
    let mut desc: Box<BwdSegDesc> = unsafe { zeroed_box() };
    desc.program[..stream.len()].copy_from_slice(&stream);
    desc.list_offset[..list_offset.len()].copy_from_slice(&list_offset);
    desc.k = k as u16;
    desc.num_foldable = num_foldable;
    desc.fold_source[..fold_source.len()].copy_from_slice(&fold_source);
    desc.source[..sources.len()].copy_from_slice(&sources);
    desc.slot[..table.len()].copy_from_slice(&table);
    desc.c_init_coeff = c_init_coeff;
    desc.immediates[..immediates.len()].copy_from_slice(&immediates);
    desc.eq_low = binding.eq_low;
    desc.contributions = binding.contributions;
    desc.eq_sizes = binding.eq_sizes;
    desc.logical_rows = logical_rows;
    Ok(desc)
}

pub(super) fn lower_bwd_seg_r0(
    program: &R0LayerProgram,
    binding: &BwdSegRoundBinding<'_>,
    k: usize,
) -> Result<BwdSegSetup, BwdSegLowerError> {
    lower_bwd_seg_view(
        SegProgramRef {
            regime: BwdRegime::R0,
            program: &program.program,
            binding: &program.binding,
        },
        binding,
        k,
    )
}

pub(super) fn lower_bwd_seg_continuation(
    program: &ContinuationLayerProgram,
    binding: &BwdSegRoundBinding<'_>,
    k: usize,
) -> Result<BwdSegSetup, BwdSegLowerError> {
    lower_bwd_seg_view(
        SegProgramRef {
            regime: BwdRegime::Ext,
            program: &program.program,
            binding: &program.binding,
        },
        binding,
        k,
    )
}

fn lower_slot(index: u8, slot: &ResolvedAddrSlot) -> Result<BwdSegAddrSlot, BwdSegLowerError> {
    if let Some(kind) = slot.procedural_kind {
        if usize::from(kind) >= BWD_COEFF_PROCEDURAL_KINDS {
            return Err(BwdSegLowerError::UnknownProceduralKind {
                window: index,
                kind,
            });
        }
        match slot.base {
            Some(column) if !column.is_e4 => {
                return Err(BwdSegLowerError::ProceduralWindowWithMatrixRead { window: index })
            }
            None if slot.columns > 1 => {
                return Err(BwdSegLowerError::MultiColumnProceduralWindow {
                    window: index,
                    columns: slot.columns,
                })
            }
            _ => {}
        }
    }
    let Some(column) = slot.base else {
        return Ok(BwdSegAddrSlot {
            base: std::ptr::null(),
            log2_stride: 0,
            origin: BWD_COEFF_ORIGIN_PROCEDURAL,
            procedural_kind: slot
                .procedural_kind
                .ok_or(BwdSegLowerError::MissingReadBacking { window: index })?,
            reserved: [0; 5],
        });
    };
    if slot.deferred_base {
        if !column.matrix_base.is_null() {
            return Err(BwdSegLowerError::NullWindowGeometry { window: index });
        }
    } else {
        check_column_geometry(index, &column)?;
    }
    let element = if column.is_e4 {
        E4_COLUMN_BYTES
    } else {
        BF_COLUMN_BYTES
    };
    if column.stride_bytes % element != 0 || !(column.stride_bytes / element).is_power_of_two() {
        return Err(BwdSegLowerError::StrideNotPowerOfTwo {
            window: index,
            stride_bytes: column.stride_bytes,
        });
    }
    let elements = column.stride_bytes / element;
    let base = column.ptr as usize;
    if base
        .checked_add(slot.columns * column.stride_bytes as usize)
        .is_none()
    {
        return Err(BwdSegLowerError::NullWindowGeometry { window: index });
    }
    Ok(BwdSegAddrSlot {
        base: if slot.deferred_base {
            std::ptr::null()
        } else {
            column.ptr
        },
        log2_stride: elements.trailing_zeros() as u8,
        origin: if column.is_e4 {
            BWD_COEFF_ORIGIN_READ_EXT
        } else {
            BWD_COEFF_ORIGIN_READ_BASE
        },
        procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
        reserved: [0; 5],
    })
}

#[allow(clippy::too_many_arguments)]
fn lower_source(
    source: usize,
    addr: &ResolvedSourceAddr,
    binding: &BwdSegRoundBinding<'_>,
    slot_columns: &[usize],
    round: u8,
    fold_depth: u8,
) -> Result<LoweredSource, BwdSegLowerError> {
    let read_slot = addr.read_slot;
    let slot = binding
        .slots
        .get(read_slot)
        .ok_or(BwdSegLowerError::SourceWindowOutOfRange {
            source,
            window: read_slot.min(u8::MAX as usize) as u8,
        })?;
    let window = read_slot as u8;
    if addr.read_column >= slot_columns[read_slot] {
        return Err(BwdSegLowerError::SourceColumnOutOfWindow {
            source,
            window,
            column: addr.read_column as u16,
        });
    }

    if addr.backing_depth > round || round - addr.backing_depth > BWD_COEFF_MAX_FOLD_DEPTH {
        return Err(BwdSegLowerError::InvalidDepths {
            window,
            backing_depth: addr.backing_depth,
            target_depth: round,
        });
    }
    let delta = round - addr.backing_depth;
    if delta > fold_depth || !(delta == 0 || delta == 1 || delta == fold_depth) {
        return Err(BwdSegLowerError::UnsupportedFoldDelta {
            window,
            delta,
            fold_depth,
        });
    }

    let origin = match (slot.procedural_kind, slot.base) {
        (_, Some(column)) if column.is_e4 => SourceOrigin::E4,
        (Some(_), Some(_)) => {
            return Err(BwdSegLowerError::ProceduralWindowWithMatrixRead { window })
        }
        (None, Some(_)) => SourceOrigin::Bf,
        (Some(_), None) => SourceOrigin::Procedural,
        (None, None) => return Err(BwdSegLowerError::MissingReadBacking { window }),
    };
    if slot.base.is_none_or(|column| !column.is_e4) && addr.backing_depth != 0 {
        return Err(BwdSegLowerError::BaseReadAtFoldedDepth {
            window,
            backing_depth: addr.backing_depth,
        });
    }
    let (class, publishes) = assign_class(origin, delta);

    if slot.base.is_some() {
        let needed = (2 * binding.rows * (1usize << delta)) as u32;
        if slot.read_elements < needed {
            return Err(BwdSegLowerError::ReadSpanOverflow {
                window,
                needed,
                have: slot.read_elements,
            });
        }
    }

    let cache = if publishes {
        let (slot_index, column) = addr
            .publish
            .ok_or(BwdSegLowerError::MissingPublishBacking { window })?;
        let target =
            binding
                .slots
                .get(slot_index)
                .ok_or(BwdSegLowerError::SourceWindowOutOfRange {
                    source,
                    window: slot_index.min(u8::MAX as usize) as u8,
                })?;
        let backing = target
            .base
            .ok_or(BwdSegLowerError::MissingPublishBacking { window })?;
        let extent = 2 * binding.rows * E4_COLUMN_BYTES as usize;
        if !backing.is_e4 || (backing.stride_bytes as usize) < extent {
            return Err(BwdSegLowerError::ExplicitPublishGeometry {
                window,
                is_e4: backing.is_e4,
                stride_bytes: backing.stride_bytes,
            });
        }
        if column >= target.columns {
            return Err(BwdSegLowerError::SourceColumnOutOfWindow {
                source,
                window: slot_index.min(u8::MAX as usize) as u8,
                column: column as u16,
            });
        }
        bwd_seg_lane(slot_index, column).ok_or(BwdSegLowerError::NullWindowGeometry { window })?
    } else {
        if addr.publish.is_some() {
            return Err(BwdSegLowerError::UnexpectedPublishBacking { window });
        }
        BWD_SEG_ADDR_NONE
    };

    let src = bwd_seg_lane(read_slot, addr.read_column)
        .ok_or(BwdSegLowerError::NullWindowGeometry { window })?;
    Ok(LoweredSource {
        record: BwdSegSourceRecord {
            src,
            cache,
            class: class.code(),
            delta,
        },
        class,
        publishes,
    })
}

fn check_column_geometry(window: u8, column: &ResolvedColumn) -> Result<(), BwdSegLowerError> {
    if column.ptr.is_null() || column.stride_bytes == 0 {
        return Err(BwdSegLowerError::NullWindowGeometry { window });
    }
    let element = if column.is_e4 {
        E4_COLUMN_BYTES
    } else {
        BF_COLUMN_BYTES
    };
    if column.stride_bytes % element != 0 {
        return Err(BwdSegLowerError::WindowStrideMismatch {
            window,
            is_e4: column.is_e4,
            stride_bytes: column.stride_bytes,
        });
    }
    Ok(())
}

// A strided set of touched column ranges for alias validation.
#[derive(Clone, Copy)]
struct StridedColumns {
    base: usize,
    stride: usize,
    count: usize,
    extent: usize,
}

impl StridedColumns {
    fn hull(&self) -> (usize, usize) {
        (
            self.base,
            self.base + (self.count - 1) * self.stride + self.extent,
        )
    }

    fn overlaps(&self, other: &StridedColumns) -> bool {
        if self.count == 0 || other.count == 0 {
            return false;
        }
        // Hull fast path: disjoint hulls cannot alias, and the hulls only
        // over-approximate when a stride exceeds its extent.
        let (a_lo, a_hi) = self.hull();
        let (b_lo, b_hi) = other.hull();
        if a_hi <= b_lo || b_hi <= a_lo {
            return false;
        }
        if self.stride == self.extent && other.stride == other.extent {
            return true;
        }
        // Interleaved hulls: judge the actual per-column extents. Quadratic,
        // but host-side, once per lowering, and only for hull-overlapping
        // pairs (in practice: column sets of one per-poly region family).
        for i in 0..self.count {
            let lo = self.base + i * self.stride;
            let hi = lo + self.extent;
            for j in 0..other.count {
                let other_lo = other.base + j * other.stride;
                if lo < other_lo + other.extent && other_lo < hi {
                    return true;
                }
            }
        }
        false
    }
}

/// Reject a launch whose publishes would clobber something it also reads.
///
/// Works on ADDRESSES, so a slot whose base is still null — a procedural slot,
/// or one whose backing is deferred to schedule time
/// ([`ResolvedAddrSlot::deferred_base`]) — is outside what this can decide and is
/// skipped. For the deferred kind that is the caller's obligation, and for the
/// production folding buffers it is structural: a round's destination buffer and
/// everything it reads are different allocations.
#[allow(clippy::too_many_arguments)]
fn check_alias(
    table: &[BwdSegAddrSlot],
    columns: &[usize],
    read_extent: &[usize],
    publishes: &[bool],
    rows: usize,
) -> Result<(), BwdSegLowerError> {
    // Per-column write extent: both endpoint halves, as E4. Read extent: the
    // pair total at the window's delta, in the backing's own width — the same
    // count `lower_window`'s span guard bounded against the backing.
    let publish_extent = 2 * rows * E4_COLUMN_BYTES as usize;
    let stride_of = |index: usize| -> usize {
        let slot = &table[index];
        let element = if slot.origin == BWD_COEFF_ORIGIN_READ_EXT {
            E4_COLUMN_BYTES
        } else {
            BF_COLUMN_BYTES
        } as usize;
        element << slot.log2_stride
    };
    let publish_of = |index: usize| -> Option<StridedColumns> {
        (publishes[index] && !table[index].base.is_null()).then_some(StridedColumns {
            base: table[index].base as usize,
            stride: stride_of(index),
            count: columns[index],
            extent: publish_extent,
        })
    };
    let read_of = |index: usize| -> Option<StridedColumns> {
        (read_extent[index] != 0 && !table[index].base.is_null()).then_some(StridedColumns {
            base: table[index].base as usize,
            stride: stride_of(index),
            count: columns[index],
            extent: read_extent[index],
        })
    };
    for index in 0..table.len() {
        let Some(publish) = publish_of(index) else {
            continue;
        };
        for other_index in 0..table.len() {
            let mut aliases = read_of(other_index).is_some_and(|read| publish.overlaps(&read));
            if other_index != index {
                aliases = aliases
                    || publish_of(other_index).is_some_and(|other| publish.overlaps(&other));
            }
            if aliases {
                return Err(BwdSegLowerError::UnsafePublishAlias {
                    window: index as u8,
                    other: other_index as u8,
                });
            }
        }
    }

    Ok(())
}

/// The category a lean class names in `regime`, or `None` for a dead class.
fn lean_category(regime: BwdRegime, class: u8) -> Option<TermCategory> {
    let table = match regime {
        BwdRegime::R0 => LEAN_R0_OPCODES,
        BwdRegime::Ext => LEAN_CONT_OPCODES,
    };
    table
        .iter()
        .find(|(listed, _)| *listed == u16::from(class))
        .map(|(_, category)| *category)
}

/// Validate one term and annotate its operand classes.
fn annotate_record(
    record: usize,
    term: &LeanTerm,
    regime: BwdRegime,
    source_classes: &[SourceClass],
) -> Result<AnnotatedTerm, BwdSegLowerError> {
    let category = lean_category(regime, term.class).ok_or(LeanCodecError::ClassNotInRegime {
        term: record,
        opcode: u16::from(term.class),
    })?;
    let class_of = |slot: u16| -> Result<SourceClass, BwdSegLowerError> {
        source_classes
            .get(usize::from(slot))
            .copied()
            .ok_or(BwdSegLowerError::SourceSlotOutOfRange { term: record, slot })
    };
    let first = class_of(term.source_a)?;
    let second = if category_arity(category) == 1 {
        if term.source_b != SOURCE_NONE {
            return Err(LeanCodecError::SourceBMustBeNone { term: record }.into());
        }
        None
    } else {
        if term.source_b == SOURCE_NONE {
            return Err(LeanCodecError::SourceBMissing { term: record }.into());
        }
        Some(class_of(term.source_b)?)
    };
    Ok(AnnotatedTerm {
        category,
        operands: [Some(first), second],
    })
}

/// Validate atoms and annotate their operands' source classes.
///
/// Singleton and header coefficients index recipes; member coefficients index
/// immediates. Headers consume a record index but produce no term.
fn annotate_atoms(
    atoms: &[LeanAtom],
    regime: BwdRegime,
    source_classes: &[SourceClass],
    coefficients: usize,
    immediates: usize,
) -> Result<Vec<SegAtom>, BwdSegLowerError> {
    if immediates > LEAN_MAX_IMMEDIATES {
        return Err(BwdSegLowerError::ImmediateTableOverflow { len: immediates });
    }
    // The literals occupy the two ids below the table, so `id` addresses the
    // table iff `RESERVED <= id < RESERVED + len`.
    let immediate_ids = usize::from(ImmediateId::RESERVED) + immediates;
    let bank = |coeff: u16| -> Result<(), BwdSegLowerError> {
        if usize::from(coeff) >= coefficients {
            return Err(BwdSegLowerError::CoefficientIndexPastBank {
                index: usize::from(coeff),
                entries: coefficients,
            });
        }
        Ok(())
    };
    let mut out = Vec::with_capacity(atoms.len());
    let mut record = 0usize;
    for atom in atoms {
        match atom {
            LeanAtom::Term(term) => {
                bank(term.coeff)?;
                out.push(SegAtom::Term(annotate_record(
                    record,
                    term,
                    regime,
                    source_classes,
                )?));
                record += 1;
            }
            LeanAtom::Group {
                core,
                has_c0,
                has_c2,
                members,
            } => {
                // R0 has no group headers at all — `decode_atoms` decodes class 2
                // there as the live `C2ProductBfBf` term class — so a group here
                // is an Ext-only shape by construction.
                debug_assert!(regime != BwdRegime::R0, "R0 decodes no group headers");
                bank(*core)?;
                let header = record;
                record += 1;
                let mut annotated = Vec::with_capacity(members.len());
                for member in members {
                    if usize::from(member.coeff) >= immediate_ids {
                        return Err(BwdSegLowerError::ImmediateOutOfRange {
                            record,
                            id: member.coeff,
                        });
                    }
                    annotated.push(SegMember {
                        annotated: annotate_record(record, member, regime, source_classes)?,
                        immediate: member.coeff,
                    });
                    record += 1;
                }
                debug_assert_eq!(record - header, 1 + members.len());
                out.push(SegAtom::Group {
                    core: *core,
                    has_c0: *has_c0,
                    has_c2: *has_c2,
                    members: annotated,
                });
            }
        }
    }
    Ok(out)
}
