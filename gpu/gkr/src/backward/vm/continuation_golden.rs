//! The continuation-binder golden DTO: a storage-independent, pointer-free
//! description of one layer's lowered continuation rounds.
//!
//! Every pointer the binder and the lowering produce is replaced by a semantic
//! origin plus a byte offset, so the DTO is a function of the compiled program
//! and the start round alone. That is what makes it a usable differential oracle
//! for the start_round-aware rework: the same layer lowered at
//! `start_round = 1` must serialize to the same bytes it did before.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use gpu_core::primitives::field::BF;
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

use crate::upstream::{GKRAddress, GKRCircuitArtifact, VirtualSetupPoly};
use crate::GkrPrograms;

// ── Canonical pointers ───────────────────────────────────────────────────────

/// The synthetic address space the snapshot resolver hands the binder. The top
/// nibble names the region, the next 20 bits name the backing, and the low 40
/// bits are the byte offset inside it.
pub(crate) const GOLDEN_REGION_SHIFT: u32 = 60;
pub(crate) const GOLDEN_TAG_SHIFT: u32 = 40;
pub(crate) const GOLDEN_OFFSET_MASK: usize = (1usize << GOLDEN_TAG_SHIFT) - 1;
pub(crate) const GOLDEN_REGION_MATRIX: usize = 1;
pub(crate) const GOLDEN_REGION_EQ_LOW: usize = 2;
pub(crate) const GOLDEN_REGION_CONTRIBUTIONS: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CanonicalPtr {
    Null,
    /// A storage matrix, named by the family tag the snapshot resolver assigned.
    Matrix {
        family: u32,
        byte_offset: u64,
    },
    EqLow {
        byte_offset: u64,
    },
    Contributions {
        byte_offset: u64,
    },
}

impl CanonicalPtr {
    pub(crate) fn of(pointer: usize) -> Self {
        if pointer == 0 {
            return Self::Null;
        }
        let region = pointer >> GOLDEN_REGION_SHIFT;
        let byte_offset = (pointer & GOLDEN_OFFSET_MASK) as u64;
        let family = ((pointer >> GOLDEN_TAG_SHIFT) & ((1 << 20) - 1)) as u32;
        match region {
            GOLDEN_REGION_MATRIX => Self::Matrix {
                family,
                byte_offset,
            },
            GOLDEN_REGION_EQ_LOW => Self::EqLow { byte_offset },
            GOLDEN_REGION_CONTRIBUTIONS => Self::Contributions { byte_offset },
            _ => panic!("the snapshot binder produced a pointer outside its address space"),
        }
    }

    fn code(&self) -> u8 {
        match self {
            Self::Null => 0,
            Self::Matrix { .. } => 1,
            Self::EqLow { .. } => 2,
            Self::Contributions { .. } => 3,
        }
    }
}

// ── Canonical addresses ──────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CanonicalAddress {
    pub kind: u8,
    pub layer: u64,
    pub offset: u64,
}

impl CanonicalAddress {
    pub(crate) fn of(address: GKRAddress) -> Self {
        let (kind, layer, offset) = match address {
            GKRAddress::BaseLayerWitness(offset) => (0, 0, offset),
            GKRAddress::BaseLayerMemory(offset) => (1, 0, offset),
            GKRAddress::Setup(offset) => (2, 0, offset),
            GKRAddress::ScratchSpace(offset) => (3, 0, offset),
            GKRAddress::InnerLayer { layer, offset } => (4, layer, offset),
            GKRAddress::Cached { layer, offset } => (5, layer, offset),
            GKRAddress::VirtualSetup(poly) => (
                6,
                0,
                match poly {
                    VirtualSetupPoly::RangeCheck16Bits => 0,
                    VirtualSetupPoly::RangeCheckTimestamp => 1,
                    VirtualSetupPoly::InitsAndTeardownsLow => 2,
                    VirtualSetupPoly::InitsAndTeardownsHigh => 3,
                },
            ),
        };
        Self {
            kind,
            layer: layer as u64,
            offset: offset as u64,
        }
    }
}

// ── The DTO ──────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalSlot {
    pub base: CanonicalPtr,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: u8,
    pub deferred_base: bool,
    pub columns: u32,
    pub read_elements: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundSourceDto {
    pub read_slot: u32,
    pub read_column: u32,
    pub publish_slot: u32,
    pub publish_column: u32,
    pub backing_depth: u8,
}

/// The `publish: None` encoding.
pub const NO_PUBLISH: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceRecordDto {
    pub src: u16,
    pub cache: u16,
    pub class: u8,
    pub delta: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldingBufferPatchDto {
    pub slot: u32,
    pub buffer_round: u8,
    pub byte_offset: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationRoundDto {
    pub absolute_round: u8,
    pub rows: u64,
    pub k: u16,
    pub num_foldable: u16,
    pub logical_rows: u32,
    pub c_init_coeff: u32,
    pub eq_high: Vec<u32>,
    pub eq_low_size: u32,
    pub eq_low: CanonicalPtr,
    pub contributions: CanonicalPtr,
    pub folding_buffer_columns: u32,
    pub folding_buffer_column_elems: u64,
    pub folding_buffer_patches: Vec<FoldingBufferPatchDto>,
    pub slots: Vec<CanonicalSlot>,
    pub sources: Vec<BoundSourceDto>,
    pub records: Vec<SourceRecordDto>,
    pub fold_source: Vec<u16>,
    pub list_offset: Vec<u16>,
    pub program: Vec<u16>,
    pub immediates: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationGoldenDto {
    pub layer: u32,
    pub start_round: u8,
    pub folding_steps: u32,
    pub rounds: Vec<ContinuationRoundDto>,
    pub final_evaluations: Vec<(CanonicalAddress, u64)>,
}

impl ContinuationGoldenDto {
    pub(crate) fn final_evaluations_from(
        evaluations: &BTreeMap<GKRAddress, usize>,
    ) -> Vec<(CanonicalAddress, u64)> {
        let mut entries: Vec<(CanonicalAddress, u64)> = evaluations
            .iter()
            .map(|(address, offset)| (CanonicalAddress::of(*address), *offset as u64))
            .collect();
        entries.sort();
        entries
    }
}

// ── The golden file ──────────────────────────────────────────────────────────

pub const GOLDEN_MAGIC: &[u8; 8] = b"GKRCONT1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoldenEntry {
    pub layout: String,
    pub dto: ContinuationGoldenDto,
}

pub fn encode_golden(entries: &[GoldenEntry]) -> Vec<u8> {
    let mut out = Writer::default();
    out.bytes(GOLDEN_MAGIC);
    out.u32(entries.len() as u32);
    for entry in entries {
        out.string(&entry.layout);
        write_dto(&mut out, &entry.dto);
    }
    out.0
}

pub fn decode_golden(bytes: &[u8]) -> Result<Vec<GoldenEntry>, String> {
    let mut input = Reader::new(bytes);
    let magic = input.bytes(GOLDEN_MAGIC.len())?;
    if magic != GOLDEN_MAGIC {
        return Err("not a continuation golden file".to_string());
    }
    let count = input.u32()? as usize;
    let mut entries = Vec::with_capacity(count);
    for _ in 0..count {
        let layout = input.string()?;
        let dto = read_dto(&mut input)?;
        entries.push(GoldenEntry { layout, dto });
    }
    if !input.done() {
        return Err("trailing bytes in the continuation golden file".to_string());
    }
    Ok(entries)
}

fn write_dto(out: &mut Writer, dto: &ContinuationGoldenDto) {
    out.u32(dto.layer);
    out.u8(dto.start_round);
    out.u32(dto.folding_steps);
    out.u32(dto.rounds.len() as u32);
    // Consecutive rounds repeat their term stream and immediates verbatim once
    // every source folds at delta 1, so those four arrays carry a
    // same-as-previous flag. The DTO stays fully materialized either way.
    let mut previous: Option<&ContinuationRoundDto> = None;
    for round in &dto.rounds {
        write_round(out, round, previous);
        previous = Some(round);
    }
    out.u32(dto.final_evaluations.len() as u32);
    for (address, offset) in &dto.final_evaluations {
        out.u8(address.kind);
        out.u64(address.layer);
        out.u64(address.offset);
        out.u64(*offset);
    }
}

fn read_dto(input: &mut Reader<'_>) -> Result<ContinuationGoldenDto, String> {
    let layer = input.u32()?;
    let start_round = input.u8()?;
    let folding_steps = input.u32()?;
    let round_count = input.u32()? as usize;
    let mut rounds: Vec<ContinuationRoundDto> = Vec::with_capacity(round_count.min(1 << 10));
    for _ in 0..round_count {
        let round = read_round(input, rounds.last())?;
        rounds.push(round);
    }
    let final_evaluations = input.repeat(|input| {
        Ok((
            CanonicalAddress {
                kind: input.u8()?,
                layer: input.u64()?,
                offset: input.u64()?,
            },
            input.u64()?,
        ))
    })?;
    Ok(ContinuationGoldenDto {
        layer,
        start_round,
        folding_steps,
        rounds,
        final_evaluations,
    })
}

fn write_round(
    out: &mut Writer,
    round: &ContinuationRoundDto,
    previous: Option<&ContinuationRoundDto>,
) {
    out.u8(round.absolute_round);
    out.u64(round.rows);
    out.u16(round.k);
    out.u16(round.num_foldable);
    out.u32(round.logical_rows);
    out.u32(round.c_init_coeff);
    out.u32(round.eq_high.len() as u32);
    for size in &round.eq_high {
        out.u32(*size);
    }
    out.u32(round.eq_low_size);
    write_ptr(out, round.eq_low);
    write_ptr(out, round.contributions);
    out.u32(round.folding_buffer_columns);
    out.u64(round.folding_buffer_column_elems);
    out.u32(round.folding_buffer_patches.len() as u32);
    for patch in &round.folding_buffer_patches {
        out.u32(patch.slot);
        out.u8(patch.buffer_round);
        out.u64(patch.byte_offset);
    }
    out.u32(round.slots.len() as u32);
    for slot in &round.slots {
        write_ptr(out, slot.base);
        out.u8(slot.log2_stride);
        out.u8(slot.origin);
        out.u8(slot.procedural_kind);
        out.u8(u8::from(slot.deferred_base));
        out.u32(slot.columns);
        out.u32(slot.read_elements);
    }
    out.u32(round.sources.len() as u32);
    for source in &round.sources {
        out.u32(source.read_slot);
        out.u32(source.read_column);
        out.u32(source.publish_slot);
        out.u32(source.publish_column);
        out.u8(source.backing_depth);
    }
    if out.same_as_previous(previous.map(|previous| &previous.records), &round.records) {
        out.u32(round.records.len() as u32);
        for record in &round.records {
            out.u16(record.src);
            out.u16(record.cache);
            out.u8(record.class);
            out.u8(record.delta);
        }
    }
    if out.same_as_previous(
        previous.map(|previous| &previous.fold_source),
        &round.fold_source,
    ) {
        out.u16_vec(&round.fold_source);
    }
    out.u16_vec(&round.list_offset);
    if out.same_as_previous(previous.map(|previous| &previous.program), &round.program) {
        out.u16_vec(&round.program);
    }
    if out.same_as_previous(
        previous.map(|previous| &previous.immediates),
        &round.immediates,
    ) {
        out.u32(round.immediates.len() as u32);
        for immediate in &round.immediates {
            out.u32(*immediate);
        }
    }
}

fn read_round(
    input: &mut Reader<'_>,
    previous: Option<&ContinuationRoundDto>,
) -> Result<ContinuationRoundDto, String> {
    let absolute_round = input.u8()?;
    let rows = input.u64()?;
    let k = input.u16()?;
    let num_foldable = input.u16()?;
    let logical_rows = input.u32()?;
    let c_init_coeff = input.u32()?;
    let eq_high = input.repeat(|input| input.u32())?;
    let eq_low_size = input.u32()?;
    let eq_low = read_ptr(input)?;
    let contributions = read_ptr(input)?;
    let folding_buffer_columns = input.u32()?;
    let folding_buffer_column_elems = input.u64()?;
    let folding_buffer_patches = input.repeat(|input| {
        Ok(FoldingBufferPatchDto {
            slot: input.u32()?,
            buffer_round: input.u8()?,
            byte_offset: input.u64()?,
        })
    })?;
    let slots = input.repeat(|input| {
        Ok(CanonicalSlot {
            base: read_ptr(input)?,
            log2_stride: input.u8()?,
            origin: input.u8()?,
            procedural_kind: input.u8()?,
            deferred_base: input.u8()? != 0,
            columns: input.u32()?,
            read_elements: input.u32()?,
        })
    })?;
    let sources = input.repeat(|input| {
        Ok(BoundSourceDto {
            read_slot: input.u32()?,
            read_column: input.u32()?,
            publish_slot: input.u32()?,
            publish_column: input.u32()?,
            backing_depth: input.u8()?,
        })
    })?;
    let records = input.reused(previous.map(|previous| &previous.records), |input| {
        input.repeat(|input| {
            Ok(SourceRecordDto {
                src: input.u16()?,
                cache: input.u16()?,
                class: input.u8()?,
                delta: input.u8()?,
            })
        })
    })?;
    let fold_source = input.reused(previous.map(|previous| &previous.fold_source), |input| {
        input.repeat(|input| input.u16())
    })?;
    let list_offset = input.repeat(|input| input.u16())?;
    let program = input.reused(previous.map(|previous| &previous.program), |input| {
        input.repeat(|input| input.u16())
    })?;
    let immediates = input.reused(previous.map(|previous| &previous.immediates), |input| {
        input.repeat(|input| input.u32())
    })?;
    Ok(ContinuationRoundDto {
        absolute_round,
        rows,
        k,
        num_foldable,
        logical_rows,
        c_init_coeff,
        eq_high,
        eq_low_size,
        eq_low,
        contributions,
        folding_buffer_columns,
        folding_buffer_column_elems,
        folding_buffer_patches,
        slots,
        sources,
        records,
        fold_source,
        list_offset,
        program,
        immediates,
    })
}

fn write_ptr(out: &mut Writer, pointer: CanonicalPtr) {
    out.u8(pointer.code());
    match pointer {
        CanonicalPtr::Null => {}
        CanonicalPtr::Matrix {
            family,
            byte_offset,
        } => {
            out.u32(family);
            out.u64(byte_offset);
        }
        CanonicalPtr::EqLow { byte_offset } | CanonicalPtr::Contributions { byte_offset } => {
            out.u64(byte_offset)
        }
    }
}

fn read_ptr(input: &mut Reader<'_>) -> Result<CanonicalPtr, String> {
    match input.u8()? {
        0 => Ok(CanonicalPtr::Null),
        1 => Ok(CanonicalPtr::Matrix {
            family: input.u32()?,
            byte_offset: input.u64()?,
        }),
        2 => Ok(CanonicalPtr::EqLow {
            byte_offset: input.u64()?,
        }),
        3 => Ok(CanonicalPtr::Contributions {
            byte_offset: input.u64()?,
        }),
        code => Err(format!("unknown canonical pointer code {code}")),
    }
}

// ── The committed corpus ─────────────────────────────────────────────────────

/// The 12 committed layouts, with the circuit type whose embedded forward
/// schedule they compile against. The `_layout_gkr` suffix is load-bearing: the
/// bare `*_gkr.json` glob matches 47 files.
pub const CONTINUATION_GOLDEN_CORPUS: &[(&str, CircuitType)] = &[
    (
        "add_sub_lui_auipc_mop_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )),
    ),
    (
        "bigint_with_extended_control_layout_gkr.json",
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
    ),
    (
        "blake2_g_function_layout_gkr.json",
        CircuitType::Delegation(DelegationCircuitType::Blake2GFunction),
    ),
    (
        "blake2_with_extended_control_layout_gkr.json",
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
    ),
    (
        "inits_and_teardowns_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
    ),
    (
        "jump_branch_slt_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::JumpBranchSlt,
        )),
    ),
    (
        "keccak_special5_layout_gkr.json",
        CircuitType::Delegation(DelegationCircuitType::KeccakSpecial5),
    ),
    (
        "mem_subword_only_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreSubwordOnly,
        )),
    ),
    (
        "mem_word_only_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        )),
    ),
    (
        "shift_binop_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::ShiftBinary,
        )),
    ),
    (
        "unified_reduced_machine_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::Unified),
    ),
    (
        "unsigned_mul_div_layout_gkr.json",
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::MulDivUnsigned,
        )),
    ),
];

pub fn continuation_golden_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("artifacts")
        .join("windowed_continuation_legacy_golden_v1.bin")
}

fn compiled_circuits_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits")
}

/// Compile one corpus layout, returning its programs and its layer count.
pub fn compile_corpus_layout(layout: &str) -> (GkrPrograms, usize) {
    let (_, circuit_type) = CONTINUATION_GOLDEN_CORPUS
        .iter()
        .find(|(name, _)| *name == layout)
        .unwrap_or_else(|| panic!("{layout} is not part of the continuation golden corpus"));
    let path = compiled_circuits_dir().join(layout);
    let bytes =
        std::fs::read(&path).unwrap_or_else(|error| panic!("reading {}: {error}", path.display()));
    let artifact: GKRCircuitArtifact<BF> = serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("parsing {}: {error}", path.display()));
    let layers = artifact.layers.len();
    let programs = GkrPrograms::compile(*circuit_type, Arc::new(artifact))
        .unwrap_or_else(|error| panic!("{layout}: {error}"));
    (programs, layers)
}

/// Compile the corpus and snapshot every layer's continuation construction at
/// `start_round = 1`. One entry per (layout, layer), in corpus order.
pub fn build_continuation_golden() -> Vec<GoldenEntry> {
    let mut entries = Vec::new();
    for (layout, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, layers) = compile_corpus_layout(layout);
        for layer in 0..layers {
            entries.push(GoldenEntry {
                layout: (*layout).to_string(),
                dto: super::production_bind::legacy_continuation_snapshot(&programs, layer),
            });
        }
    }
    entries
}

// ── A minimal little-endian codec ────────────────────────────────────────────

#[derive(Default)]
struct Writer(Vec<u8>);

impl Writer {
    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    fn u16(&mut self, value: u16) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }

    fn bytes(&mut self, value: &[u8]) {
        self.0.extend_from_slice(value);
    }

    fn string(&mut self, value: &str) {
        self.u32(value.len() as u32);
        self.bytes(value.as_bytes());
    }

    fn u16_vec(&mut self, values: &[u16]) {
        self.u32(values.len() as u32);
        for value in values {
            self.u16(*value);
        }
    }

    /// Emit the reuse flag; the caller writes the payload only when this returns
    /// `true`.
    fn same_as_previous<T: PartialEq>(&mut self, previous: Option<&Vec<T>>, current: &[T]) -> bool {
        let fresh = previous.is_none_or(|previous| previous.as_slice() != current);
        self.u8(u8::from(fresh));
        fresh
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn done(&self) -> bool {
        self.at == self.bytes.len()
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], String> {
        let end = self.at + count;
        if end > self.bytes.len() {
            return Err(format!(
                "golden file truncated: wanted {count} bytes at {}",
                self.at
            ));
        }
        let slice = &self.bytes[self.at..end];
        self.at = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, String> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn bytes(&mut self, count: usize) -> Result<&'a [u8], String> {
        self.take(count)
    }

    fn string(&mut self) -> Result<String, String> {
        let len = self.u32()? as usize;
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec()).map_err(|error| error.to_string())
    }

    fn reused<T: Clone>(
        &mut self,
        previous: Option<&Vec<T>>,
        read: impl FnOnce(&mut Self) -> Result<Vec<T>, String>,
    ) -> Result<Vec<T>, String> {
        if self.u8()? != 0 {
            return read(self);
        }
        previous
            .cloned()
            .ok_or_else(|| "the first round cannot reuse a previous array".to_string())
    }

    fn repeat<T>(
        &mut self,
        mut read: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<Vec<T>, String> {
        let count = self.u32()? as usize;
        let mut values = Vec::with_capacity(count.min(1 << 16));
        for _ in 0..count {
            values.push(read(self)?);
        }
        Ok(values)
    }
}

/// The builder-level differential for the start_round-aware continuation, and
/// the round-3 construction the windowed arm will drive.
#[cfg(test)]
mod cpu_continuation_rebase {
    use super::super::production_bind::{continuation_snapshot, drained_eq_sizes};
    use super::super::seg_desc::BWD_COEFF_ORIGIN_READ_BASE;
    use super::*;
    use crate::backward::make_eq_sizes;

    /// Round 3 is the windowed arm's handoff: `BWD_SEG_MAX_FOLD_DEPTH`.
    const WINDOW_START_ROUND: u8 = 3;

    #[test]
    fn every_corpus_layer_reproduces_the_committed_golden() {
        let path = continuation_golden_path();
        let committed = decode_golden(
            &std::fs::read(&path)
                .unwrap_or_else(|error| panic!("reading {}: {error}", path.display())),
        )
        .expect("decoding the committed golden");
        let recomputed = build_continuation_golden();
        assert_eq!(
            committed.len(),
            recomputed.len(),
            "the corpus changed shape: {} committed entries vs {} recomputed",
            committed.len(),
            recomputed.len()
        );
        for (want, got) in committed.iter().zip(&recomputed) {
            assert_eq!(want.layout, got.layout);
            assert_eq!(want.dto.layer, got.dto.layer, "{}", want.layout);
            assert_eq!(want.dto.start_round, got.dto.start_round, "{}", want.layout);
            assert_eq!(
                want.dto.rounds.len(),
                got.dto.rounds.len(),
                "{} layer {}",
                want.layout,
                want.dto.layer
            );
            for (want_round, got_round) in want.dto.rounds.iter().zip(&got.dto.rounds) {
                assert_eq!(
                    want_round, got_round,
                    "{} layer {} round {}",
                    want.layout, want.dto.layer, want_round.absolute_round
                );
            }
            assert_eq!(
                want.dto.final_evaluations, got.dto.final_evaluations,
                "{} layer {} final evaluations",
                want.layout, want.dto.layer
            );
        }
    }

    fn assert_round_three_start(layout: &str, expected_folding_steps: u32) {
        let (programs, layers) = compile_corpus_layout(layout);
        let mut saw_raw_base_read = false;
        for layer in 0..layers {
            let dto = continuation_snapshot(&programs, layer, WINDOW_START_ROUND);
            let label = format!("{layout} layer {layer}");
            assert_eq!(dto.folding_steps, expected_folding_steps, "{label}");
            assert_eq!(dto.start_round, WINDOW_START_ROUND, "{label}");
            assert_eq!(
                dto.rounds.len(),
                (expected_folding_steps - u32::from(WINDOW_START_ROUND)) as usize,
                "{label}: rounds run [start_round, folding_steps)"
            );

            let base = make_eq_sizes(dto.folding_steps as usize - usize::from(WINDOW_START_ROUND));
            for (index, round) in dto.rounds.iter().enumerate() {
                let absolute = WINDOW_START_ROUND + index as u8;
                assert_eq!(round.absolute_round, absolute, "{label}: absolute round");
                assert_eq!(
                    round.rows,
                    1u64 << (dto.folding_steps - u32::from(absolute) - 1),
                    "{label} round {absolute}: rows"
                );
                assert_eq!(
                    round.logical_rows as u64, round.rows,
                    "{label} round {absolute}: the descriptor's row count"
                );

                // Eq metadata: the producer's base, drained by this round's
                // position in the sequence.
                let drained = drained_eq_sizes(base, absolute - WINDOW_START_ROUND + 1);
                assert_eq!(
                    round.eq_high,
                    drained.high.to_vec(),
                    "{label} round {absolute}: eq high slabs"
                );
                assert_eq!(
                    round.eq_low_size, drained.low,
                    "{label} round {absolute}: eq low slab"
                );

                // Deltas: round 3 reads every source straight out of storage at
                // the publication depth; every later round reads the preceding
                // round's buffer at depth 1.
                let expected_depth = if absolute == WINDOW_START_ROUND {
                    0
                } else {
                    absolute - 1
                };
                let expected_delta = absolute - expected_depth;
                for source in &round.sources {
                    assert_eq!(
                        source.backing_depth, expected_depth,
                        "{label} round {absolute}: backing depth"
                    );
                }
                for record in &round.records {
                    assert_eq!(
                        record.delta, expected_delta,
                        "{label} round {absolute}: fold delta"
                    );
                }

                // Buffer lifetimes: a round writes its own buffer and reads at
                // most the immediately preceding one.
                assert_eq!(
                    round.folding_buffer_columns as usize,
                    round.sources.len(),
                    "{label} round {absolute}: every source publishes"
                );
                assert_eq!(
                    round.folding_buffer_column_elems,
                    2 * round.rows,
                    "{label} round {absolute}: buffer column length"
                );
                for patch in &round.folding_buffer_patches {
                    assert!(
                        patch.buffer_round == absolute
                            || (absolute > WINDOW_START_ROUND
                                && patch.buffer_round == absolute - 1),
                        "{label} round {absolute}: patch names buffer round {}",
                        patch.buffer_round
                    );
                }
                if absolute == WINDOW_START_ROUND {
                    assert!(
                        round
                            .folding_buffer_patches
                            .iter()
                            .all(|patch| patch.buffer_round == absolute),
                        "{label} round {absolute}: the first round has no prior buffer"
                    );
                    saw_raw_base_read |= round
                        .slots
                        .iter()
                        .any(|slot| slot.origin == BWD_COEFF_ORIGIN_READ_BASE);
                }
                assert!(
                    !round.sources.is_empty(),
                    "{label} round {absolute}: a coordinate with no sources proves nothing"
                );
            }

            assert!(
                !dto.final_evaluations.is_empty(),
                "{label}: the last round must publish the layer's final evaluations"
            );

            // Once every source folds at depth 1, the windowed sequence and the
            // per-round sequence are the same construction.
            let per_round = continuation_snapshot(&programs, layer, 1);
            for round in dto.rounds.iter().skip(1) {
                let mirror = per_round
                    .rounds
                    .iter()
                    .find(|candidate| candidate.absolute_round == round.absolute_round)
                    .unwrap_or_else(|| {
                        panic!("{label}: no per-round round {}", round.absolute_round)
                    });
                assert_eq!(
                    strip_eq(round),
                    strip_eq(mirror),
                    "{label} round {}: the two arms diverge after the handoff",
                    round.absolute_round
                );
            }
            assert_eq!(
                dto.final_evaluations, per_round.final_evaluations,
                "{label}: the final gather offsets must not depend on the start round"
            );
        }
        assert!(
            saw_raw_base_read,
            "{layout}: no layer reads a base-field backing raw at the handoff round, \
             so the depth-3 raw read is untested"
        );
    }

    /// The two arms are compared modulo the eq schedule, which is exactly what
    /// the start round changes.
    fn strip_eq(round: &ContinuationRoundDto) -> ContinuationRoundDto {
        let mut stripped = round.clone();
        stripped.eq_high = Vec::new();
        stripped.eq_low_size = 0;
        stripped
    }

    #[test]
    fn round_three_start_constructs_for_a_log_24_layer() {
        assert_round_three_start("add_sub_lui_auipc_mop_layout_gkr.json", 24);
    }

    #[test]
    fn round_three_start_constructs_for_a_log_20_layer() {
        assert_round_three_start("blake2_with_extended_control_layout_gkr.json", 20);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_golden_codec_round_trips() {
        let entries = vec![GoldenEntry {
            layout: "probe_layout_gkr.json".to_string(),
            dto: ContinuationGoldenDto {
                layer: 2,
                start_round: 1,
                folding_steps: 24,
                rounds: vec![ContinuationRoundDto {
                    absolute_round: 1,
                    rows: 4,
                    k: 8,
                    num_foldable: 2,
                    logical_rows: 4,
                    c_init_coeff: 7,
                    eq_high: vec![1, 2],
                    eq_low_size: 3,
                    eq_low: CanonicalPtr::EqLow { byte_offset: 16 },
                    contributions: CanonicalPtr::Contributions { byte_offset: 0 },
                    folding_buffer_columns: 3,
                    folding_buffer_column_elems: 8,
                    folding_buffer_patches: vec![FoldingBufferPatchDto {
                        slot: 1,
                        buffer_round: 1,
                        byte_offset: 128,
                    }],
                    slots: vec![CanonicalSlot {
                        base: CanonicalPtr::Matrix {
                            family: 5,
                            byte_offset: 64,
                        },
                        log2_stride: 20,
                        origin: 0,
                        procedural_kind: 0xff,
                        deferred_base: false,
                        columns: 2,
                        read_elements: 1 << 20,
                    }],
                    sources: vec![BoundSourceDto {
                        read_slot: 0,
                        read_column: 1,
                        publish_slot: NO_PUBLISH,
                        publish_column: NO_PUBLISH,
                        backing_depth: 0,
                    }],
                    records: vec![SourceRecordDto {
                        src: 3,
                        cache: 9,
                        class: 1,
                        delta: 1,
                    }],
                    fold_source: vec![1, 0],
                    list_offset: vec![0, 3, 6],
                    program: vec![1, 2, 3, 4, 5, 6],
                    immediates: vec![9, 10],
                }],
                final_evaluations: vec![(
                    CanonicalAddress {
                        kind: 4,
                        layer: 1,
                        offset: 7,
                    },
                    256,
                )],
            },
        }];
        let bytes = encode_golden(&entries);
        assert_eq!(decode_golden(&bytes).unwrap(), entries);
    }

    #[test]
    fn cpu_canonical_pointers_decode_their_regions() {
        let matrix = (GOLDEN_REGION_MATRIX << GOLDEN_REGION_SHIFT) | (7 << GOLDEN_TAG_SHIFT) | 96;
        assert_eq!(
            CanonicalPtr::of(matrix),
            CanonicalPtr::Matrix {
                family: 7,
                byte_offset: 96
            }
        );
        assert_eq!(CanonicalPtr::of(0), CanonicalPtr::Null);
        assert_eq!(
            CanonicalPtr::of((GOLDEN_REGION_EQ_LOW << GOLDEN_REGION_SHIFT) | 32),
            CanonicalPtr::EqLow { byte_offset: 32 }
        );
    }
}
