//! Task-8-only prepared-state differential support.
//!
//! This module is excluded from normal and `no_cuda` builds. It borrows the
//! production-owned main-entry storage and never exports that owner.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeAccessor};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::{
    alloc_static_pinned_box_from_slice, alloc_static_pinned_box_uninit, StaticPinnedBox,
};
use gpu_gkr_compiler::{MainContinuationWindowProgram, SourceId};
use gpu_prover_context::PoolMemoryHighWaterReport;
use gpu_prover_context::ProverContext;

use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, get_main_layer_claim_point_device_ptr,
    launch_backward_dual_finalize_from_partials, launch_build_eq_high_and_low_groups_from_point,
    make_eq_sizes, record_active_eq_slot_fold, resolve_active_eq_slot, warp_partial_count,
    GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::backward::main_continuation::abi::MAIN_CONTINUATION_WINDOW_TENSOR_CELLS;
use crate::backward::main_continuation::binding::{
    bind_first_main_continuation_window, bind_later_main_continuation_window,
    launch_main_continuation_window, MainContinuationWindowRuntimeScratch,
};
use crate::backward::main_continuation::{ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::main_layer::execution_plan::main_continuation_post_tail_eq_boundary;
use crate::backward::stage_snapshots::{
    MainContinuationDifferentialReport, Task8ContinuationDifferentialRequest,
};
use crate::backward::task8_probe::{
    task8_enqueue, task8_register_symbol, task8_symbol, Task8EnqueueKind, Task8ProbeGuard,
    Task8Span,
};
use crate::backward::vm::production_bind::{
    canonicalize_legacy_publication, family_read_place, prepare_continuation_differential_bank,
    prepare_continuation_differential_rounds, BwdSegBankFillSpans,
    LegacyPublicationCanonicalizationError, Task8LivePublicationEvent,
};
use crate::backward::vm::seg::launch_bwd_seg_build_fold_weights;
use crate::backward::vm::seg_coeff_eval::{
    BWD_SEG_BLOB_MONOMIALS_OFFSET, BWD_SEG_CHALLENGE_CLAIM_BATCHING,
};
use crate::backward::window::binding::window_partials_len;
use crate::backward::window::tail::{launch_window_tensor_round_tail, WindowTailState};
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::forward::vm::production_bind::resolve_storage_column;
use crate::upstream::{Field, GKRAddress, PrimeField};
use crate::{
    BackwardExecutionStrategy, GkrBackwardOptions, GkrPrograms, GpuGKRStorage, WindowTailArm,
};

pub(crate) const TASK8_DIAGNOSTIC: &str = "task8-main-continuation-prepared-differential-v1";

const TASK8_READBACK_CHUNK_BYTES: usize = 16 << 20;
const TASK8_WINDOW_ARM: &str = "window";
const TASK8_LEGACY_ARM: &str = "legacy";
const TASK8_SHARED_DEVICE_SYMBOLS: [&str; 3] = [
    "claim_point_symbol",
    "eq_high_symbol",
    "fold_weights_symbol",
];
const TASK8_RESIDENT_COEFFICIENT_BANK: &str =
    "the coefficient bank a previous fill left in place, which the legacy arm's prior passes read before its own fill";
const TASK8_PRODUCTION_STORAGE: &str =
    "production-owned trace storage the differential borrows and never writes";
const TASK8_NON_PUBLICATION_COMPARISONS: usize =
    12 + 3 + 8 + 1 + 1 + 2 * GKR_EQ_GROUP_TABLE_LEN * (1 + GKR_EQ_HIGH_SLOTS) + 3;

/// What one ledger row states about the byte range it names. Every row comes
/// from a span the enqueue reported before it ran.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8QueuedUse {
    /// Covers bytes for the first time.
    Write,
    /// Reads bytes an earlier record of this generation covered.
    Read,
    /// Reads bytes this generation never wrote: content the buffer or symbol
    /// already held. Never counted as initialization.
    ResidentRead,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8LedgerRecord {
    step: u64,
    enqueue: u64,
    position: usize,
    site: &'static str,
    role: &'static str,
    address: usize,
    range: std::ops::Range<usize>,
    use_kind: Task8QueuedUse,
}

/// Names one generation of one owner. Every ledger operation takes a token, so
/// a repeated owner address can never bind an operation to a different
/// generation than the caller holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Task8GenerationToken {
    slot: usize,
    owner: usize,
    generation: u64,
}

/// Where a generation's bytes come from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8OwnerOrigin {
    /// The arm allocates or writes the owner itself, so it starts uncovered.
    ArmOwned,
    /// Production storage the arm only reads. It starts fully covered and every
    /// write or mutation of it is rejected.
    Borrowed(&'static str),
    /// A factored Eq table: the arm writes the active prefix each build fixes
    /// and reads back the whole buffer, so bytes outside its own writes are
    /// recorded as resident reads and never as initialization.
    FactoredEq,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8OwnerGeneration {
    arm: &'static str,
    label: &'static str,
    owner: usize,
    covered: std::ops::Range<usize>,
    generation: u64,
    origin: Task8OwnerOrigin,
    superseded_by: Option<u64>,
    initialized: Vec<std::ops::Range<usize>>,
    final_enqueue: Option<u64>,
    records: Vec<Task8LedgerRecord>,
}

impl Task8OwnerGeneration {
    fn within(&self, range: &std::ops::Range<usize>) -> bool {
        range.start <= range.end
            && range.start >= self.covered.start
            && range.end <= self.covered.end
    }

    fn absorb(coverage: &mut Vec<std::ops::Range<usize>>, range: std::ops::Range<usize>) {
        if range.start == range.end {
            return;
        }
        let mut merged = range;
        coverage.retain(|covered| {
            if covered.start > merged.end || merged.start > covered.end {
                return true;
            }
            merged.start = merged.start.min(covered.start);
            merged.end = merged.end.max(covered.end);
            false
        });
        coverage.push(merged);
        coverage.sort_by_key(|covered| covered.start);
    }

    fn holds(coverage: &[std::ops::Range<usize>], range: &std::ops::Range<usize>) -> bool {
        range.start == range.end
            || coverage
                .iter()
                .any(|covered| covered.start <= range.start && range.end <= covered.end)
    }

    fn disjoint(coverage: &[std::ops::Range<usize>], range: &std::ops::Range<usize>) -> bool {
        coverage
            .iter()
            .all(|covered| covered.start >= range.end || range.start >= covered.end)
    }

    /// The parts of `range` no record of this generation has covered.
    fn gaps(&self, range: &std::ops::Range<usize>) -> Vec<std::ops::Range<usize>> {
        let mut gaps = Vec::new();
        let mut cursor = range.start;
        for covered in &self.initialized {
            if covered.end <= cursor || covered.start >= range.end {
                continue;
            }
            if covered.start > cursor {
                gaps.push(cursor..covered.start);
            }
            cursor = cursor.max(covered.end);
        }
        if cursor < range.end {
            gaps.push(cursor..range.end);
        }
        gaps
    }

    fn last_enqueue(&self) -> Option<u64> {
        self.records.last().map(|record| record.enqueue)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8LedgerError {
    StaleToken,
    AmbiguousLiveGeneration,
    UseAfterFinal,
    UseBeforeInitialization,
    ResidentReadOfCoveredBytes,
    ResidentReadOfNonEqOwner,
    WriteToBorrowedOwner,
    UnownedSpan,
    ReuseWithoutFinal,
    FinalWithoutEnqueue,
    FinalAlreadyBound,
}

/// Enqueue-order ledger for the device buffers and symbols one differential
/// coordinate's two arms name.
///
/// The ledger never opens an enqueue of its own. Every enqueue and every
/// pointer span in it is reported by [`crate::backward::task8_probe`] from a
/// scope the production call site opens *before* the launch or copy runs, so
/// the recorded order is the order the runtime received the work.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Task8OwnerGenerationLedger {
    next_step: u64,
    next_generation: u64,
    enqueues: Vec<Task8AbsorbedEnqueue>,
    generations: Vec<Task8OwnerGeneration>,
}

/// One enqueue as the probe reported it, plus how many of its spans the ledger
/// bound to an owner.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8AbsorbedEnqueue {
    ordinal: u64,
    /// The ordinal the arm's own probe gave this enqueue.
    probe_ordinal: u64,
    arm: &'static str,
    site: &'static str,
    kind: Task8EnqueueKind,
    records: usize,
    issued_at_open: u64,
    issued_at_close: u64,
}

impl Task8OwnerGenerationLedger {
    fn resolve(&self, token: Task8GenerationToken) -> Result<usize, Task8LedgerError> {
        let entry = self
            .generations
            .get(token.slot)
            .ok_or(Task8LedgerError::StaleToken)?;
        if entry.owner != token.owner || entry.generation != token.generation {
            return Err(Task8LedgerError::StaleToken);
        }
        Ok(token.slot)
    }

    /// The single generation an address is currently open under, or `None` when
    /// the address has never been opened. Two open generations at one address
    /// are a ledger fault, not a lookup to disambiguate by position.
    fn live_generation(
        &self,
        owner: usize,
    ) -> Result<Option<Task8GenerationToken>, Task8LedgerError> {
        let mut live = self
            .generations
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.owner == owner && entry.superseded_by.is_none());
        let first = live.next();
        if live.next().is_some() {
            return Err(Task8LedgerError::AmbiguousLiveGeneration);
        }
        Ok(first.map(|(slot, entry)| Task8GenerationToken {
            slot,
            owner,
            generation: entry.generation,
        }))
    }

    /// The generation that owns `range`: the most specific declaration
    /// containing it, so a sub-buffer such as the reduced tensor takes the spans
    /// inside it from the allocation it lives in.
    ///
    /// The most specific declaration stays authoritative after it binds `Final`.
    /// A span inside a finalized narrow owner is a use after that owner's last
    /// enqueue even while a broader owner is still live, until an explicit
    /// successor generation is admitted at the same address. Two live
    /// candidates of the same width are a ledger fault, not a choice.
    fn owner_of(&self, range: &std::ops::Range<usize>) -> Result<usize, Task8LedgerError> {
        let mut narrowest: Option<usize> = None;
        let mut live: Option<usize> = None;
        let mut ambiguous = false;
        for (slot, entry) in self.generations.iter().enumerate() {
            if !entry.within(range) {
                continue;
            }
            let width = entry.covered.end - entry.covered.start;
            let open = entry.superseded_by.is_none() && entry.final_enqueue.is_none();
            match narrowest {
                Some(best) if best < width => continue,
                Some(best) if best == width => {
                    if open {
                        ambiguous |= live.is_some();
                        live = Some(slot);
                    }
                }
                _ => {
                    narrowest = Some(width);
                    ambiguous = false;
                    live = open.then_some(slot);
                }
            }
        }
        if ambiguous {
            return Err(Task8LedgerError::AmbiguousLiveGeneration);
        }
        match (narrowest, live) {
            (_, Some(slot)) => Ok(slot),
            (Some(_), None) => Err(Task8LedgerError::UseAfterFinal),
            (None, None) => Err(Task8LedgerError::UnownedSpan),
        }
    }

    fn open(
        &mut self,
        arm: &'static str,
        label: &'static str,
        origin: Task8OwnerOrigin,
        owner: usize,
        bytes: usize,
    ) -> Result<Task8GenerationToken, Task8LedgerError> {
        let covered = owner..owner + bytes;
        match self.live_generation(owner)? {
            None => Ok(self.register(arm, label, origin, covered)),
            Some(prior) => self.admit_reuse(arm, label, origin, prior, covered),
        }
    }

    fn register(
        &mut self,
        arm: &'static str,
        label: &'static str,
        origin: Task8OwnerOrigin,
        covered: std::ops::Range<usize>,
    ) -> Task8GenerationToken {
        self.next_generation += 1;
        let token = Task8GenerationToken {
            slot: self.generations.len(),
            owner: covered.start,
            generation: self.next_generation,
        };
        let initialized = match origin {
            Task8OwnerOrigin::ArmOwned | Task8OwnerOrigin::FactoredEq => Vec::new(),
            Task8OwnerOrigin::Borrowed(_) => vec![covered.clone()],
        };
        self.generations.push(Task8OwnerGeneration {
            arm,
            label,
            owner: covered.start,
            covered,
            generation: self.next_generation,
            origin,
            superseded_by: None,
            initialized,
            final_enqueue: None,
            records: Vec::new(),
        });
        token
    }

    /// The only admission a repeated owner address has. The caller names the
    /// generation it is retiring; that generation must still be the open one and
    /// must have bound `Final` to its own last enqueue, so no queued use of it
    /// can remain. The successor starts with no coverage of its own.
    fn admit_reuse(
        &mut self,
        arm: &'static str,
        label: &'static str,
        origin: Task8OwnerOrigin,
        prior: Task8GenerationToken,
        covered: std::ops::Range<usize>,
    ) -> Result<Task8GenerationToken, Task8LedgerError> {
        let slot = self.resolve(prior)?;
        if self.live_generation(prior.owner)? != Some(prior) {
            return Err(Task8LedgerError::StaleToken);
        }
        {
            let entry = &self.generations[slot];
            let bound = entry
                .final_enqueue
                .ok_or(Task8LedgerError::ReuseWithoutFinal)?;
            if entry.last_enqueue() != Some(bound) {
                return Err(Task8LedgerError::ReuseWithoutFinal);
            }
        }
        let token = self.register(arm, label, origin, covered);
        self.generations[slot].superseded_by = Some(token.generation);
        Ok(token)
    }

    /// Binds one span an enqueue reported to the generation that owns it.
    fn record(
        &mut self,
        enqueue: &Task8AbsorbedEnqueue,
        role: &'static str,
        address: usize,
        bytes: usize,
        use_kind: Task8QueuedUse,
    ) -> Result<u64, Task8LedgerError> {
        let range = address..address + bytes;
        let slot = self.owner_of(&range)?;
        {
            let entry = &self.generations[slot];
            if entry.arm != enqueue.arm {
                return Err(Task8LedgerError::UnownedSpan);
            }
            match use_kind {
                Task8QueuedUse::Write => {
                    if matches!(entry.origin, Task8OwnerOrigin::Borrowed(_)) {
                        return Err(Task8LedgerError::WriteToBorrowedOwner);
                    }
                }
                Task8QueuedUse::Read => {
                    if !Task8OwnerGeneration::holds(&entry.initialized, &range) {
                        return Err(Task8LedgerError::UseBeforeInitialization);
                    }
                }
                Task8QueuedUse::ResidentRead => {
                    if !matches!(entry.origin, Task8OwnerOrigin::FactoredEq) {
                        return Err(Task8LedgerError::ResidentReadOfNonEqOwner);
                    }
                    if !Task8OwnerGeneration::disjoint(&entry.initialized, &range) {
                        return Err(Task8LedgerError::ResidentReadOfCoveredBytes);
                    }
                }
            }
        }
        let step = self.next_step;
        self.next_step += 1;
        let position = self.enqueues[enqueue.ordinal as usize].records;
        self.enqueues[enqueue.ordinal as usize].records += 1;
        let entry = &mut self.generations[slot];
        if use_kind == Task8QueuedUse::Write {
            Task8OwnerGeneration::absorb(&mut entry.initialized, range.clone());
        }
        entry.records.push(Task8LedgerRecord {
            step,
            enqueue: enqueue.ordinal,
            position,
            site: enqueue.site,
            role,
            address,
            range,
            use_kind,
        });
        Ok(step)
    }

    /// Binds `Final` to the enqueue of the generation's own last pointer use.
    fn bind_final(&mut self, owner: Task8GenerationToken) -> Result<u64, Task8LedgerError> {
        let slot = self.resolve(owner)?;
        let entry = &mut self.generations[slot];
        if entry.final_enqueue.is_some() {
            return Err(Task8LedgerError::FinalAlreadyBound);
        }
        let bound = entry
            .last_enqueue()
            .ok_or(Task8LedgerError::FinalWithoutEnqueue)?;
        entry.final_enqueue = Some(bound);
        Ok(bound)
    }

    fn generation(&self, owner: Task8GenerationToken) -> &Task8OwnerGeneration {
        &self.generations[self.resolve(owner).expect("Task 8 ledger token is stale")]
    }

    fn labelled(&self, label: &'static str) -> Vec<&Task8OwnerGeneration> {
        self.generations
            .iter()
            .filter(|entry| entry.label == label)
            .collect()
    }

    fn arm_labels(&self, arm: &'static str) -> BTreeSet<&'static str> {
        self.generations
            .iter()
            .filter(|entry| entry.arm == arm)
            .map(|entry| entry.label)
            .collect()
    }

    fn label_generations(&self, arm: &'static str, label: &'static str) -> usize {
        self.generations
            .iter()
            .filter(|entry| entry.arm == arm && entry.label == label)
            .count()
    }

    /// How many rows record a read of bytes the generation never wrote.
    fn resident_reads(&self, arm: &'static str) -> usize {
        self.generations
            .iter()
            .filter(|entry| entry.arm == arm)
            .flat_map(|entry| entry.records.iter())
            .filter(|record| record.use_kind == Task8QueuedUse::ResidentRead)
            .count()
    }

    fn enqueue_sites(&self, arm: &'static str) -> std::collections::BTreeMap<&'static str, usize> {
        let mut sites = std::collections::BTreeMap::new();
        for enqueue in self.enqueues.iter().filter(|enqueue| enqueue.arm == arm) {
            *sites.entry(enqueue.site).or_insert(0) += 1;
        }
        sites
    }

    /// Takes every enqueue the probe observed since the last absorption and
    /// binds each reported span to the generation that owns those bytes.
    fn absorb(&mut self, arm: &'static str, probe: &Task8ProbeGuard) {
        for observed in probe.drain() {
            let ordinal = self.enqueues.len() as u64;
            let expected = self
                .enqueues
                .iter()
                .rev()
                .find(|enqueue| enqueue.arm == arm)
                .map_or(0, |enqueue| enqueue.probe_ordinal + 1);
            assert_eq!(
                observed.ordinal, expected,
                "Task 8 absorbed an enqueue out of the probe's order"
            );
            let closed = observed
                .issued_at_close
                .expect("Task 8 absorbed an enqueue that never closed");
            assert_eq!(
                observed.issued_at_open, observed.ordinal,
                "Task 8 enqueue {} was opened after work it should precede",
                observed.site
            );
            let enqueue = Task8AbsorbedEnqueue {
                ordinal,
                probe_ordinal: observed.ordinal,
                arm,
                site: observed.site,
                kind: observed.kind,
                records: 0,
                issued_at_open: observed.issued_at_open,
                issued_at_close: closed,
            };
            self.enqueues.push(enqueue.clone());
            for span in &observed.spans {
                let use_kind = if span.write {
                    Task8QueuedUse::Write
                } else if span.resident {
                    Task8QueuedUse::ResidentRead
                } else {
                    Task8QueuedUse::Read
                };
                self.record(&enqueue, span.role, span.address, span.bytes, use_kind)
                    .unwrap_or_else(|error| {
                        panic!(
                            "Task 8 {arm} arm {} span {} at {:#x}+{}: {error:?}",
                            observed.site, span.role, span.address, span.bytes
                        )
                    });
            }
        }
    }
}

/// One owner the arm holds open.
#[derive(Clone, Copy, Debug)]
struct Task8LedgerOwner {
    token: Task8GenerationToken,
    arm: &'static str,
    label: &'static str,
    base: usize,
    bytes: usize,
}

fn ledger_open(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    label: &'static str,
    origin: Task8OwnerOrigin,
    base: usize,
    bytes: usize,
) -> Task8LedgerOwner {
    let token = ledger
        .open(arm, label, origin, base, bytes)
        .unwrap_or_else(|error| panic!("Task 8 {arm} arm could not open {label}: {error:?}"));
    Task8LedgerOwner {
        token,
        arm,
        label,
        base,
        bytes,
    }
}

fn ledger_open_allocation<T>(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    label: &'static str,
    allocation: &DeviceSlice<T>,
) -> Task8LedgerOwner {
    ledger_open(
        ledger,
        arm,
        label,
        Task8OwnerOrigin::ArmOwned,
        allocation.as_ptr() as usize,
        allocation.len() * std::mem::size_of::<T>(),
    )
}

fn ledger_bind_final(ledger: &mut Task8OwnerGenerationLedger, owner: &Task8LedgerOwner) -> u64 {
    ledger.bind_final(owner.token).unwrap_or_else(|error| {
        let (arm, label) = (owner.arm, owner.label);
        panic!("Task 8 {arm} arm could not bind Final to {label}: {error:?}")
    })
}

/// Splits a whole-buffer readback of a factored Eq owner into the bytes this
/// arm's builds wrote and the bytes the buffer already held. Nothing is marked
/// initialized: the resident part is recorded as a resident read.
fn eq_readback_spans(
    ledger: &Task8OwnerGenerationLedger,
    owner: &Task8LedgerOwner,
) -> Vec<Task8Span> {
    let entry = ledger.generation(owner.token);
    let whole = owner.base..owner.base + owner.bytes;
    let mut spans = Vec::new();
    for covered in &entry.initialized {
        let start = covered.start.max(whole.start);
        let end = covered.end.min(whole.end);
        if start < end {
            spans.push(Task8Span::read(owner.label, start, end - start));
        }
    }
    for gap in entry.gaps(&whole) {
        spans.push(Task8Span::resident_read(
            owner.label,
            gap.start,
            gap.end - gap.start,
        ));
    }
    spans.sort_by_key(|span| span.address);
    spans
}

/// The census one enqueue must carry, checked against the records the ledger
/// holds for it. Each rule is a property of the native kernel the site
/// launches, so an omitted or widened range at that site fails here rather than
/// passing as a merely well-formed record stream.
fn validate_enqueue_census(ledger: &Task8OwnerGenerationLedger) {
    let element = std::mem::size_of::<E4>();
    let owner_span = |record: &Task8LedgerRecord| {
        ledger
            .generations
            .iter()
            .find(|entry| entry.records.iter().any(|held| held.step == record.step))
            .map(|entry| entry.covered.clone())
            .expect("every record belongs to a generation")
    };
    for (ordinal, enqueue) in ledger.enqueues.iter().enumerate() {
        let records: Vec<&Task8LedgerRecord> = ledger
            .generations
            .iter()
            .flat_map(|entry| entry.records.iter())
            .filter(|record| record.enqueue == ordinal as u64)
            .collect();
        let named = |role: &str, use_kind: Task8QueuedUse| {
            records
                .iter()
                .filter(|record| record.role == role && record.use_kind == use_kind)
                .count()
        };
        match enqueue.site {
            "fold-weight-build" => {
                let claim: Vec<_> = records
                    .iter()
                    .filter(|record| {
                        record.role == "ab_gkr_main_layer_claim_point"
                            && record.use_kind == Task8QueuedUse::Read
                    })
                    .collect();
                assert_eq!(
                    claim.len(),
                    1,
                    "a fold-weight build reads the claim point exactly once"
                );
                assert!(
                    claim[0].range.len() <= 3 * element,
                    "a fold-weight build reads at most the three coordinates below its round"
                );
                assert_eq!(
                    named("bwd_seg_fold_weights", Task8QueuedUse::Write),
                    1,
                    "a fold-weight build fills the bank once"
                );
            }
            "coefficient-bank-fill" => {
                let tables: Vec<_> = records
                    .iter()
                    .filter(|record| {
                        record.role == "coefficient_tables"
                            && record.use_kind == Task8QueuedUse::Read
                    })
                    .collect();
                let base = tables
                    .first()
                    .map(|record| owner_span(record).start)
                    .expect("a coefficient fill reads its staged tables");
                assert!(
                    tables
                        .iter()
                        .any(|record| record.address - base < BWD_SEG_BLOB_MONOMIALS_OFFSET),
                    "a coefficient fill reads its live recipe records"
                );
                assert!(
                    tables
                        .iter()
                        .any(|record| record.address - base >= BWD_SEG_BLOB_MONOMIALS_OFFSET),
                    "a coefficient fill reads the monomials its recipes reference"
                );
                let slab: Vec<_> = records
                    .iter()
                    .filter(|record| {
                        record.role == "challenge_slab" && record.use_kind == Task8QueuedUse::Read
                    })
                    .collect();
                let slab_base = slab
                    .first()
                    .map(|record| owner_span(record).start)
                    .expect("a coefficient fill reads its challenge slab");
                assert!(
                    slab.iter().any(|record| record.address - slab_base
                        == BWD_SEG_CHALLENGE_CLAIM_BATCHING as usize * element),
                    "a coefficient fill reads the batching slot every monomial scales by"
                );
                assert_eq!(
                    named("coefficient_bank", Task8QueuedUse::Write),
                    1,
                    "a coefficient fill writes the bank prefix once"
                );
            }
            "window-launch" | "segmented-round" => {
                let runs: Vec<_> = records
                    .iter()
                    .filter(|record| {
                        record.role == "bwd_seg_fold_weights"
                            && record.use_kind == Task8QueuedUse::Read
                    })
                    .collect();
                assert!(
                    !runs.is_empty(),
                    "a folding launch reads the fold-weight runs its deltas name"
                );
                for record in &runs {
                    assert!(
                        record.range.len() < owner_span(record).len(),
                        "a folding launch reads its own runs, not the whole fold-weight bank"
                    );
                }
                assert_eq!(
                    named("ab_gkr_bwd_seg_coeff_bank", Task8QueuedUse::Read),
                    1,
                    "a folding launch reads the coefficient bank once"
                );
                assert_eq!(
                    named("published_column", Task8QueuedUse::Write),
                    named("published_column", Task8QueuedUse::Read),
                    "every published column the launch writes is read back in the same launch"
                );
            }
            _ => {}
        }
    }
}

/// Replays a coordinate's ledger and checks the census each enqueue must carry.
/// Returns the confirmed shared-symbol transitions.
fn validate_owner_generation_ledger(
    ledger: &Task8OwnerGenerationLedger,
    first_arm: &'static str,
    second_arm: &'static str,
    shared_symbols: &[&'static str],
) -> usize {
    let transitions =
        validate_owner_generation_structure(ledger, first_arm, second_arm, shared_symbols);
    validate_enqueue_census(ledger);
    transitions
}

/// The recorded stream itself. Every record is checked against the coverage its
/// own generation held when that record was made, the record stream is checked
/// against the enqueue stream the probe observed, `Final` is checked against
/// each generation's exact last enqueue, and each shared device symbol is
/// checked for its two-arm generation transition.
fn validate_owner_generation_structure(
    ledger: &Task8OwnerGenerationLedger,
    first_arm: &'static str,
    second_arm: &'static str,
    shared_symbols: &[&'static str],
) -> usize {
    assert!(
        !ledger.generations.is_empty(),
        "Task 8 ledger recorded no owner generation"
    );
    assert!(
        !ledger.enqueues.is_empty(),
        "Task 8 ledger recorded no enqueue"
    );
    let mut arm_seen: Vec<&'static str> = Vec::new();
    for (ordinal, enqueue) in ledger.enqueues.iter().enumerate() {
        assert_eq!(
            enqueue.ordinal, ordinal as u64,
            "Task 8 enqueue ordinals are not dense"
        );
        assert!(
            enqueue.arm == first_arm || enqueue.arm == second_arm,
            "Task 8 enqueue {} came from an unexpected arm {}",
            enqueue.site,
            enqueue.arm
        );
        assert_eq!(
            enqueue.issued_at_open, enqueue.probe_ordinal,
            "Task 8 enqueue {} was opened after work it should precede",
            enqueue.site
        );
        assert_eq!(
            enqueue.issued_at_close,
            enqueue.probe_ordinal + 1,
            "Task 8 enqueue {} closed around work that was not its own",
            enqueue.site
        );
        assert_eq!(
            enqueue.records == 0,
            enqueue.kind == Task8EnqueueKind::Callback,
            "Task 8 enqueue {} names the wrong number of pointers for a {:?}",
            enqueue.site,
            enqueue.kind
        );
        if arm_seen.last() != Some(&enqueue.arm) {
            assert!(
                !arm_seen.contains(&enqueue.arm),
                "Task 8 arm {} resumed after the other arm started",
                enqueue.arm
            );
            arm_seen.push(enqueue.arm);
        }
    }
    assert_eq!(
        arm_seen,
        vec![first_arm, second_arm],
        "Task 8 arms did not run in the reviewed order"
    );
    let mut stream: Vec<(u64, &Task8LedgerRecord, &Task8OwnerGeneration)> = Vec::new();
    for entry in &ledger.generations {
        assert!(
            entry.arm == first_arm || entry.arm == second_arm,
            "Task 8 ledger generation {} came from an unexpected arm {}",
            entry.generation,
            entry.arm
        );
        let mut coverage = match entry.origin {
            Task8OwnerOrigin::ArmOwned | Task8OwnerOrigin::FactoredEq => Vec::new(),
            Task8OwnerOrigin::Borrowed(_) => vec![entry.covered.clone()],
        };
        let mut previous = None;
        for record in &entry.records {
            if let Some(previous) = previous {
                assert!(
                    record.step > previous,
                    "Task 8 {} records are out of ledger order",
                    entry.label
                );
            }
            previous = Some(record.step);
            stream.push((record.step, record, entry));
            assert!(
                entry.within(&record.range),
                "Task 8 {} record leaves the owner's byte range",
                entry.label
            );
            assert_eq!(
                record.address, record.range.start,
                "Task 8 {} record address and byte range disagree",
                entry.label
            );
            assert!(
                (record.enqueue as usize) < ledger.enqueues.len(),
                "Task 8 {} record names an enqueue the probe never reported",
                entry.label
            );
            assert_eq!(
                ledger.enqueues[record.enqueue as usize].arm, entry.arm,
                "Task 8 {} record crosses arms",
                entry.label
            );
            assert_eq!(
                ledger.enqueues[record.enqueue as usize].site, record.site,
                "Task 8 {} record was moved to another enqueue",
                entry.label
            );
            match record.use_kind {
                Task8QueuedUse::Write => {
                    assert!(
                        !matches!(entry.origin, Task8OwnerOrigin::Borrowed(_)),
                        "Task 8 {} wrote borrowed production storage",
                        entry.label
                    );
                    Task8OwnerGeneration::absorb(&mut coverage, record.range.clone());
                }
                Task8QueuedUse::Read => assert!(
                    Task8OwnerGeneration::holds(&coverage, &record.range),
                    "Task 8 {} used bytes its generation had not covered",
                    entry.label
                ),
                Task8QueuedUse::ResidentRead => {
                    assert!(
                        matches!(entry.origin, Task8OwnerOrigin::FactoredEq),
                        "Task 8 {} recorded a resident read outside the factored Eq tables",
                        entry.label
                    );
                    assert!(
                        Task8OwnerGeneration::disjoint(&coverage, &record.range),
                        "Task 8 {} recorded a resident read of bytes it had written",
                        entry.label
                    );
                }
            }
        }
        assert_eq!(
            coverage, entry.initialized,
            "Task 8 {} coverage replay disagrees with the ledger",
            entry.label
        );
        let bound = entry
            .final_enqueue
            .unwrap_or_else(|| panic!("Task 8 {} never bound Final", entry.label));
        assert_eq!(
            entry.last_enqueue(),
            Some(bound),
            "Task 8 {} bound Final away from its last enqueue",
            entry.label
        );
    }
    stream.sort_by_key(|(step, _, _)| *step);
    assert_eq!(
        stream.len() as u64,
        ledger.next_step,
        "Task 8 ledger step count and record count disagree"
    );
    let mut enqueue_positions = vec![0usize; ledger.enqueues.len()];
    let mut highest = None;
    for (index, (step, record, entry)) in stream.iter().enumerate() {
        assert_eq!(
            *step, index as u64,
            "Task 8 ledger steps are not the dense record order"
        );
        if let Some(highest) = highest {
            assert!(
                record.enqueue >= highest,
                "Task 8 {} record runs against the enqueue order",
                entry.label
            );
        }
        highest = Some(record.enqueue);
        let position = &mut enqueue_positions[record.enqueue as usize];
        assert_eq!(
            record.position, *position,
            "Task 8 {} record is out of position inside its enqueue",
            entry.label
        );
        *position += 1;
    }
    for (ordinal, position) in enqueue_positions.iter().enumerate() {
        assert_eq!(
            *position, ledger.enqueues[ordinal].records,
            "Task 8 enqueue {} lost a pointer record",
            ledger.enqueues[ordinal].site
        );
    }
    let mut transitions = 0;
    for label in shared_symbols {
        let generations = ledger.labelled(label);
        assert_eq!(
            generations.len(),
            2,
            "Task 8 shared symbol {label} did not record one generation per arm"
        );
        let (first, second) = (generations[0], generations[1]);
        assert_eq!(first.arm, first_arm);
        assert_eq!(second.arm, second_arm);
        assert_eq!(first.owner, second.owner);
        assert_eq!(
            first.superseded_by,
            Some(second.generation),
            "Task 8 shared symbol {label} did not retire its first generation"
        );
        assert!(second.superseded_by.is_none());
        assert!(
            first.final_enqueue.unwrap() < second.records[0].enqueue,
            "Task 8 shared symbol {label} reused an address before its Final"
        );
        transitions += 1;
    }
    transitions
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8AllocationRecord {
    kind: &'static str,
    owner: usize,
    size_bytes: usize,
    successful_requested_bytes: usize,
    physical_backing_delta_bytes: i128,
    logical_live_delta_bytes: i128,
    multiplicity: usize,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
    retired: bool,
}

fn allocation_record<T>(
    kind: &'static str,
    allocation: &DeviceSlice<T>,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
) -> Task8AllocationRecord {
    let size_bytes = allocation
        .len()
        .checked_mul(std::mem::size_of::<T>())
        .expect("Task 8 allocation byte count overflowed usize");
    Task8AllocationRecord {
        kind,
        owner: allocation.as_ptr() as usize,
        size_bytes,
        successful_requested_bytes: size_bytes,
        physical_backing_delta_bytes: 0,
        logical_live_delta_bytes: 0,
        multiplicity: 1,
        live_from,
        live_until,
        overlap_group,
        placement,
        retired: true,
    }
}

fn allocation_record_with_usage<T>(
    kind: &'static str,
    allocation: &DeviceSlice<T>,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
    before: gpu_prover_context::PoolMemoryUsage,
    after: gpu_prover_context::PoolMemoryUsage,
) -> Task8AllocationRecord {
    let mut record = allocation_record(
        kind,
        allocation,
        live_from,
        live_until,
        overlap_group,
        placement,
    );
    record.physical_backing_delta_bytes =
        signed_snapshot_delta(after.physical_backing_bytes, before.physical_backing_bytes);
    record.logical_live_delta_bytes =
        signed_snapshot_delta(after.logical_live_bytes, before.logical_live_bytes);
    record
}

fn allocation_group_record(
    kind: &'static str,
    owner: usize,
    live_from: usize,
    live_until: usize,
    overlap_group: usize,
    placement: &'static str,
    multiplicity: usize,
    report: &PoolMemoryHighWaterReport,
) -> Task8AllocationRecord {
    let physical_backing_delta_bytes = signed_snapshot_delta(
        report.return_to_entry.physical_backing_bytes,
        report.start.physical_backing_bytes,
    );
    let logical_live_delta_bytes = signed_snapshot_delta(
        report.return_to_entry.logical_live_bytes,
        report.start.logical_live_bytes,
    );
    Task8AllocationRecord {
        kind,
        owner,
        size_bytes: report.summed_requested_bytes,
        successful_requested_bytes: report.summed_requested_bytes,
        physical_backing_delta_bytes,
        logical_live_delta_bytes,
        multiplicity,
        live_from,
        live_until,
        overlap_group,
        placement,
        retired: true,
    }
}

#[inline]
fn signed_snapshot_delta(after: usize, before: usize) -> i128 {
    (after as i128) - (before as i128)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8SourceFieldClass {
    Base,
    Extension,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Task8SourceSampleValues {
    Base(Vec<BF>),
    Extension(Vec<E4>),
}

struct ScheduledSourceIdentityRecord {
    source: SourceId,
    address: GKRAddress,
    field_class: Task8SourceFieldClass,
    backing_base: usize,
    view_offset: usize,
    stride_bytes: usize,
    backing_bytes: usize,
    backing_requested_bytes: usize,
    samples: ScheduledSourceSampleValues,
}

enum ScheduledSourceSampleValues {
    Base(Vec<ScheduledReadback<BF>>),
    Extension(Vec<ScheduledReadback<E4>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8SourceIdentityRecord {
    source: SourceId,
    address: GKRAddress,
    field_class: Task8SourceFieldClass,
    backing_base: usize,
    view_offset: usize,
    stride_bytes: usize,
    backing_bytes: usize,
    backing_requested_bytes: usize,
    samples: Task8SourceSampleValues,
}

impl ScheduledSourceIdentityRecord {
    fn materialize(self) -> Task8SourceIdentityRecord {
        let samples = match self.samples {
            ScheduledSourceSampleValues::Base(values) => Task8SourceSampleValues::Base(
                values
                    .into_iter()
                    .flat_map(ScheduledReadback::materialize)
                    .collect(),
            ),
            ScheduledSourceSampleValues::Extension(values) => Task8SourceSampleValues::Extension(
                values
                    .into_iter()
                    .flat_map(ScheduledReadback::materialize)
                    .collect(),
            ),
        };
        Task8SourceIdentityRecord {
            source: self.source,
            address: self.address,
            field_class: self.field_class,
            backing_base: self.backing_base,
            view_offset: self.view_offset,
            stride_bytes: self.stride_bytes,
            backing_bytes: self.backing_bytes,
            backing_requested_bytes: self.backing_requested_bytes,
            samples,
        }
    }
}

#[derive(Clone, Debug)]
struct EqObservation {
    sizes: GkrEqSizes,
    low: Vec<E4>,
    high: Vec<E4>,
}

#[derive(Clone, Debug)]
struct PreparedObservation {
    publication: Vec<E4>,
    coefficients: Vec<E4>,
    challenges: Vec<E4>,
    seed: Vec<u32>,
    claim: Vec<E4>,
    eq_prefactor: Vec<E4>,
    pre_eq: EqObservation,
    post_eq: EqObservation,
    boundary: (u8, u8, GkrEqSizes),
}

struct ScheduledReadback<T> {
    values: Arc<Mutex<Vec<T>>>,
    expected_len: usize,
}

impl<T> ScheduledReadback<T> {
    fn materialize(self) -> Vec<T> {
        let mut values = self.values.lock().expect("Task 8 readback mutex poisoned");
        assert_eq!(
            values.len(),
            self.expected_len,
            "Task 8 readback callback census is incomplete"
        );
        std::mem::take(&mut *values)
    }
}

struct ScheduledEqObservation {
    sizes: GkrEqSizes,
    low: ScheduledReadback<E4>,
    high: ScheduledReadback<E4>,
}

struct ScheduledLiveMutationEvidence {
    e4: Vec<(
        &'static str,
        Task8LiveMutationTarget,
        E4,
        ScheduledReadback<E4>,
    )>,
    u32: Vec<(
        &'static str,
        Task8LiveMutationTarget,
        u32,
        ScheduledReadback<u32>,
    )>,
    prior_original: Option<ScheduledReadback<E4>>,
}

#[derive(Clone, Copy)]
enum Task8LiveMutationTarget {
    Publication(usize),
    Coefficient(usize),
    Challenge(usize),
    Seed(usize),
    Claim(usize),
    EqPrefactor(usize),
    PostEqLow(usize),
    PriorPublication,
}

enum Task8MaterializedLiveMutation {
    E4(&'static str, Task8LiveMutationTarget, E4),
    U32(&'static str, Task8LiveMutationTarget, u32),
}

impl ScheduledLiveMutationEvidence {
    fn empty() -> Self {
        Self {
            e4: Vec::new(),
            u32: Vec::new(),
            prior_original: None,
        }
    }

    fn materialize(self) -> Vec<Task8MaterializedLiveMutation> {
        let prior_original =
            self.prior_original
                .map(ScheduledReadback::materialize)
                .map(|values| {
                    assert_eq!(values.len(), 1);
                    values[0]
                });
        let mut mutations = Vec::new();
        for (family, target, expected, values) in self.e4 {
            assert_eq!(values.materialize(), [expected]);
            if matches!(target, Task8LiveMutationTarget::PriorPublication) {
                let original = prior_original
                    .expect("Task 8 prior-cell mutation lost its pre-adoption readback");
                assert_ne!(
                    original, expected,
                    "Task 8 prior-cell mutation did not change the live prior"
                );
            }
            mutations.push(Task8MaterializedLiveMutation::E4(family, target, expected));
        }
        for (family, target, expected, values) in self.u32 {
            assert_eq!(values.materialize(), [expected]);
            mutations.push(Task8MaterializedLiveMutation::U32(family, target, expected));
        }
        mutations
    }
}

impl ScheduledEqObservation {
    fn materialize(self) -> EqObservation {
        EqObservation {
            sizes: self.sizes,
            low: self.low.materialize(),
            high: self.high.materialize(),
        }
    }
}

struct ScheduledPreparedObservation {
    publication: ScheduledReadback<E4>,
    coefficients: ScheduledReadback<E4>,
    challenges: ScheduledReadback<E4>,
    seed: ScheduledReadback<u32>,
    claim: ScheduledReadback<E4>,
    eq_prefactor: ScheduledReadback<E4>,
    pre_eq: ScheduledEqObservation,
    post_eq: ScheduledEqObservation,
    boundary: (u8, u8, GkrEqSizes),
    memory: PoolMemoryHighWaterReport,
    allocations: Vec<Task8AllocationRecord>,
    live_mutations: ScheduledLiveMutationEvidence,
}

#[derive(Clone, Debug)]
struct Task8AdoptionEvidence {
    had_prior: bool,
    input_live_before: bool,
    first_deltas: Vec<u8>,
    first_reads_only_published: bool,
    input_retired: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8AdoptionEvidenceError {
    UnexpectedPriorState,
    Delta,
    ReadSet,
    Retirement,
}

fn validate_adoption_evidence(
    evidence: &Task8AdoptionEvidence,
) -> Result<(), Task8AdoptionEvidenceError> {
    if !evidence.had_prior {
        return Ok(());
    }
    if !evidence.input_live_before {
        return Err(Task8AdoptionEvidenceError::UnexpectedPriorState);
    }
    if evidence.first_deltas.is_empty() || evidence.first_deltas.iter().any(|delta| *delta != 3) {
        return Err(Task8AdoptionEvidenceError::Delta);
    }
    if !evidence.first_reads_only_published {
        return Err(Task8AdoptionEvidenceError::ReadSet);
    }
    if !evidence.input_retired {
        return Err(Task8AdoptionEvidenceError::Retirement);
    }
    Ok(())
}

fn validate_adoption_mutations(evidence: &Task8AdoptionEvidence) -> (usize, BTreeSet<String>) {
    validate_adoption_evidence(evidence).expect("Task 8 live adoption evidence is invalid");
    if !evidence.had_prior {
        return (0, BTreeSet::new());
    }
    let mut delta = evidence.clone();
    delta.first_deltas[0] = 2;
    assert_eq!(
        validate_adoption_evidence(&delta),
        Err(Task8AdoptionEvidenceError::Delta)
    );
    let mut read_set = evidence.clone();
    read_set.first_reads_only_published = false;
    assert_eq!(
        validate_adoption_evidence(&read_set),
        Err(Task8AdoptionEvidenceError::ReadSet)
    );
    let mut retirement = evidence.clone();
    retirement.input_retired = false;
    assert_eq!(
        validate_adoption_evidence(&retirement),
        Err(Task8AdoptionEvidenceError::Retirement)
    );
    (
        3,
        ["seeded-adoption-delta-3", "zero-remainder-take"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
    )
}

impl ScheduledPreparedObservation {
    fn materialize(
        self,
    ) -> (
        PreparedObservation,
        PoolMemoryHighWaterReport,
        Vec<Task8AllocationRecord>,
        ScheduledLiveMutationEvidence,
    ) {
        (
            PreparedObservation {
                publication: self.publication.materialize(),
                coefficients: self.coefficients.materialize(),
                challenges: self.challenges.materialize(),
                seed: self.seed.materialize(),
                claim: self.claim.materialize(),
                eq_prefactor: self.eq_prefactor.materialize(),
                pre_eq: self.pre_eq.materialize(),
                post_eq: self.post_eq.materialize(),
                boundary: self.boundary,
            },
            self.memory,
            self.allocations,
            self.live_mutations,
        )
    }
}

/// Uploads a host buffer. The copy opens its own pre-enqueue scope, so the
/// ledger sees it in the same stream order as every production enqueue.
fn upload<T: Copy>(
    context: &ProverContext,
    host: &[T],
) -> CudaResult<(DeviceAllocation<T>, StaticPinnedBox<T>)> {
    let staging = alloc_static_pinned_box_from_slice(host)?;
    let mut device = context.alloc(host.len().max(1), AllocationPlacement::BestFit)?;
    let destination = device.as_ptr() as usize;
    crate::backward::task8_enqueue_scope!(_task8, "host-upload", Copy, {
        vec![Task8Span::write(
            "upload",
            destination,
            host.len() * std::mem::size_of::<T>(),
        )]
    });
    memory_copy_async(
        &mut device[..host.len()],
        &staging[..],
        context.get_exec_stream(),
    )?;
    Ok((device, staging))
}

/// Writes the main-layer claim-point symbol and registers the address this copy
/// hands the runtime, so later launches that read the symbol without naming it
/// can record an exact range against it.
fn write_claim_point_symbol(
    context: &ProverContext,
    point: &[E4],
) -> CudaResult<(StaticPinnedBox<E4>, usize)> {
    let staging = alloc_static_pinned_box_from_slice(point)?;
    let symbol = get_main_layer_claim_point_device_ptr();
    // SAFETY: the main-layer claim-point symbol is sized for every admitted
    // folding width; the corpus maximum is pinned independently by preflight.
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(symbol, point.len()) };
    let bytes = point.len() * std::mem::size_of::<E4>();
    task8_register_symbol("ab_gkr_main_layer_claim_point", symbol as usize, bytes);
    crate::backward::task8_enqueue_scope!(_task8, "claim-point-symbol-write", Copy, {
        vec![Task8Span::write(
            "claim_point_symbol",
            symbol as usize,
            bytes,
        )]
    });
    memory_copy_async(destination, &staging[..], context.get_exec_stream())?;
    Ok((staging, symbol as usize))
}

/// Reads a device range back in scratch-sized chunks. Each chunk copy and each
/// ordering callback opens its own pre-enqueue scope; `spans` supplies the exact
/// span list for the chunk that starts at the given byte offset.
fn schedule_read_device_chunked<T, S>(
    source: &DeviceSlice<T>,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
    site: &'static str,
    mut spans: S,
) -> CudaResult<ScheduledReadback<T>>
where
    T: Copy + Default + Send + Sync + 'static,
    S: FnMut(usize, usize) -> Vec<Task8Span>,
{
    assert_eq!(scratch.len(), TASK8_READBACK_CHUNK_BYTES);
    assert_eq!(
        (scratch.as_ptr() as usize) % std::mem::align_of::<T>(),
        0,
        "Task 8 shared readback scratch lost type alignment"
    );
    let chunk_elements = (scratch.len() / std::mem::size_of::<T>()).max(1);
    let expected_len = source.len();
    let output = Arc::new(Mutex::new(Vec::new()));
    if source.is_empty() {
        return Ok(ScheduledReadback {
            values: output,
            expected_len: 0,
        });
    }
    let accessor = UnsafeAccessor::new(&scratch[..]);
    for offset in (0..source.len()).step_by(chunk_elements) {
        let len = chunk_elements.min(source.len() - offset);
        let byte_len = len
            .checked_mul(std::mem::size_of::<T>())
            .expect("Task 8 readback byte count overflowed usize");
        // SAFETY: the scratch base alignment is checked above and byte_len is
        // exactly `len * size_of::<T>()`.
        let host_chunk =
            unsafe { std::slice::from_raw_parts_mut(scratch.as_mut_ptr().cast::<T>(), len) };
        {
            let chunk_spans = spans(offset * std::mem::size_of::<T>(), byte_len);
            crate::backward::task8_enqueue_scope!(_task8, site, Copy, chunk_spans);
            memory_copy_async(
                host_chunk,
                &source[offset..offset + len],
                context.get_exec_stream(),
            )?;
        }
        let callback_output = Arc::clone(&output);
        crate::backward::task8_enqueue_scope!(_task8, "readback-ordering", Callback, Vec::new());
        callbacks.schedule(
            move || unsafe {
                let mut output = callback_output
                    .lock()
                    .expect("Task 8 readback mutex poisoned");
                if offset == 0 {
                    output
                        .try_reserve_exact(expected_len)
                        .unwrap_or_else(|error| {
                            panic!(
                            "Task 8 readback could not reserve {expected_len} elements: {error}"
                        )
                        });
                }
                assert_eq!(
                    output.len(),
                    offset,
                    "Task 8 chunk callbacks executed out of order"
                );
                let bytes = &accessor.get()[..byte_len];
                let values = std::slice::from_raw_parts(bytes.as_ptr().cast::<T>(), len);
                output.extend_from_slice(values);
            },
            context.get_exec_stream(),
        )?;
    }
    Ok(ScheduledReadback {
        values: output,
        expected_len,
    })
}

/// Reads a whole owner back, recording each chunk against it.
fn schedule_owner_readback<T>(
    source: &DeviceSlice<T>,
    owner: &Task8LedgerOwner,
    site: &'static str,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledReadback<T>>
where
    T: Copy + Default + Send + Sync + 'static,
{
    let (label, base) = (owner.label, owner.base);
    schedule_read_device_chunked(
        source,
        scratch,
        callbacks,
        context,
        site,
        |offset, bytes| vec![Task8Span::read(label, base + offset, bytes)],
    )
}

/// Reads back both factored Eq tables. The high table is addressed through the
/// symbol pointer the arm's own Eq builds already handed the runtime, never a
/// fresh symbol lookup, and each readback is split into the bytes this arm's
/// builds wrote and the bytes the buffer already held.
#[allow(clippy::too_many_arguments)]
fn schedule_read_all_eq(
    sizes: GkrEqSizes,
    eq_low: &DeviceAllocation<E4>,
    owners: &Task8ArmOwners,
    site: &'static str,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
    ledger: &Task8OwnerGenerationLedger,
) -> CudaResult<ScheduledEqObservation> {
    // SAFETY: the high Eq symbol is a contiguous two-table device region.
    let high = unsafe {
        DeviceSlice::from_raw_parts(
            owners.eq_high.base as *const E4,
            GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
        )
    };
    let low_spans = record_eq_readback_spans(ledger, owners, true);
    let high_spans = record_eq_readback_spans(ledger, owners, false);
    let low = schedule_read_device_chunked(
        eq_low,
        scratch,
        callbacks,
        context,
        site,
        |offset, bytes| chunk_spans(&low_spans, owners.eq_low.base + offset, bytes),
    )?;
    let high =
        schedule_read_device_chunked(high, scratch, callbacks, context, site, |offset, bytes| {
            chunk_spans(&high_spans, owners.eq_high.base + offset, bytes)
        })?;
    Ok(ScheduledEqObservation { sizes, low, high })
}

/// Clips a prepared span list to the byte range one chunk copies.
fn chunk_spans(spans: &[Task8Span], start: usize, bytes: usize) -> Vec<Task8Span> {
    let end = start + bytes;
    spans
        .iter()
        .filter_map(|span| {
            let clipped_start = span.address.max(start);
            let clipped_end = (span.address + span.bytes).min(end);
            (clipped_start < clipped_end).then(|| Task8Span {
                address: clipped_start,
                bytes: clipped_end - clipped_start,
                ..*span
            })
        })
        .collect()
}

fn deterministic_e4(tag: u32) -> E4 {
    E4::from_array_of_base(core::array::from_fn(|lane| {
        BF::from_u32_with_reduction(tag.wrapping_mul(17).wrapping_add(lane as u32 + 1))
    }))
}

struct TranscriptBuffers {
    seed: DeviceAllocation<u32>,
    claim: DeviceAllocation<E4>,
    prefactor: DeviceAllocation<E4>,
    coefficients: DeviceAllocation<E4>,
    challenges: DeviceAllocation<E4>,
    _seed_staging: StaticPinnedBox<u32>,
    _claim_staging: StaticPinnedBox<E4>,
    _prefactor_staging: StaticPinnedBox<E4>,
    allocations: Vec<Task8AllocationRecord>,
}

fn transcript_buffers(context: &ProverContext) -> CudaResult<TranscriptBuffers> {
    let mut allocations = Vec::new();
    let seed_host = [0x1020_3040, 0x5060_7080, 1, 2, 3, 5, 8, 13];
    let before_seed = context.get_device_memory_usage();
    let (seed, seed_staging) = upload(context, &seed_host)?;
    let after_seed = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "transcript_seed",
        &seed,
        4,
        8,
        2,
        "best_fit",
        before_seed,
        after_seed,
    ));
    let before_claim = after_seed;
    let (claim, claim_staging) = upload(context, &[deterministic_e4(0x51)])?;
    let after_claim = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "transcript_claim",
        &claim,
        4,
        8,
        2,
        "best_fit",
        before_claim,
        after_claim,
    ));
    let before_prefactor = after_claim;
    let (prefactor, prefactor_staging) = upload(context, &[deterministic_e4(0x71)])?;
    let after_prefactor = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "transcript_prefactor",
        &prefactor,
        4,
        8,
        2,
        "best_fit",
        before_prefactor,
        after_prefactor,
    ));
    let before_coefficients = after_prefactor;
    let coefficients = context.alloc(12, AllocationPlacement::BestFit)?;
    let after_coefficients = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "coefficients",
        &coefficients,
        4,
        8,
        2,
        "best_fit",
        before_coefficients,
        after_coefficients,
    ));
    let before_challenges = after_coefficients;
    let challenges = context.alloc(3, AllocationPlacement::BestFit)?;
    let after_challenges = context.get_device_memory_usage();
    allocations.push(allocation_record_with_usage(
        "challenges",
        &challenges,
        4,
        8,
        2,
        "best_fit",
        before_challenges,
        after_challenges,
    ));
    Ok(TranscriptBuffers {
        seed,
        claim,
        prefactor,
        coefficients,
        challenges,
        _seed_staging: seed_staging,
        _claim_staging: claim_staging,
        _prefactor_staging: prefactor_staging,
        allocations,
    })
}

fn open_transcript_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    transcript: &TranscriptBuffers,
) -> Task8TranscriptOwners {
    Task8TranscriptOwners {
        seed: ledger_open_allocation(ledger, arm, "transcript_seed", &transcript.seed),
        claim: ledger_open_allocation(ledger, arm, "transcript_claim", &transcript.claim),
        prefactor: ledger_open_allocation(
            ledger,
            arm,
            "transcript_prefactor",
            &transcript.prefactor,
        ),
        coefficients: ledger_open_allocation(ledger, arm, "coefficients", &transcript.coefficients),
        challenges: ledger_open_allocation(ledger, arm, "challenges", &transcript.challenges),
    }
}

fn retain_in_callback<T: Send + Sync + 'static>(
    value: T,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    crate::backward::task8_enqueue_scope!(_task8, "staging-retention", Callback, Vec::new());
    callbacks.schedule(
        move || {
            let _ = &value;
        },
        context.get_exec_stream(),
    )
}

/// Overwrites one live device cell and reads it straight back. The cell is
/// addressed through its owner, so the mutation copy and the readback copy are
/// both recorded against the exact element they name.
#[allow(clippy::too_many_arguments)]
fn schedule_live_device_mutation<T>(
    family: &'static str,
    target: Task8LiveMutationTarget,
    owner: &Task8LedgerOwner,
    offset: usize,
    value: T,
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<(
    &'static str,
    Task8LiveMutationTarget,
    T,
    ScheduledReadback<T>,
)>
where
    T: Copy + Default + Send + Sync + 'static,
{
    let element = std::mem::size_of::<T>();
    let address = owner.base + offset * element;
    assert!(address + element <= owner.base + owner.bytes);
    let staging = alloc_static_pinned_box_from_slice(&[value])?;
    // SAFETY: the owner's geometry is the allocation or symbol this cell lives
    // in, and `offset` is inside it.
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(address as *mut T, 1) };
    let label = owner.label;
    {
        crate::backward::task8_enqueue_scope!(_task8, "live-mutation", Copy, {
            vec![Task8Span::write(label, address, element)]
        });
        memory_copy_async(destination, &staging[..], context.get_exec_stream())?;
    }
    let readback = schedule_read_device_chunked(
        destination,
        readback_scratch,
        callbacks,
        context,
        "live-mutation-readback",
        |chunk, bytes| vec![Task8Span::read(label, address + chunk, bytes)],
    )?;
    retain_in_callback(staging, callbacks, context)?;
    Ok((family, target, value, readback))
}

/// Uploads the four challenge buffers and opens their owners.
#[allow(clippy::type_complexity)]
fn upload_challenges(
    context: &ProverContext,
    ledger: &mut Task8OwnerGenerationLedger,
    probe: &Task8ProbeGuard,
    arm: &'static str,
    external_host: &[E4],
) -> CudaResult<(
    DeviceAllocation<E4>,
    DeviceAllocation<E4>,
    DeviceAllocation<E4>,
    DeviceAllocation<E4>,
    (
        StaticPinnedBox<E4>,
        StaticPinnedBox<E4>,
        StaticPinnedBox<E4>,
        StaticPinnedBox<E4>,
    ),
    Task8ChallengeOwners,
)> {
    let (external, external_staging) = upload(context, external_host)?;
    let external_owner = ledger_open_allocation(ledger, arm, "external_challenges", &external);
    ledger.absorb(arm, probe);
    let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
    let lookup_mul_owner =
        ledger_open_allocation(ledger, arm, "lookup_multiplicative", &lookup_mul);
    ledger.absorb(arm, probe);
    let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
    let lookup_add_owner = ledger_open_allocation(ledger, arm, "lookup_additive", &lookup_add);
    ledger.absorb(arm, probe);
    let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
    let batching_owner = ledger_open_allocation(ledger, arm, "claim_batching", &batching);
    ledger.absorb(arm, probe);
    Ok((
        external,
        lookup_mul,
        lookup_add,
        batching,
        (
            external_staging,
            lookup_mul_staging,
            lookup_add_staging,
            batching_staging,
        ),
        Task8ChallengeOwners {
            external: external_owner,
            lookup_multiplicative: lookup_mul_owner,
            lookup_additive: lookup_add_owner,
            claim_batching: batching_owner,
        },
    ))
}

/// Opens the challenge slab and staged-table owners from the spans the fill
/// itself reported, and the coefficient bank from the symbol it registered.
fn open_bank_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    owners: &mut Task8ArmOwners,
    spans: BwdSegBankFillSpans,
) -> (Task8LedgerOwner, Task8LedgerOwner) {
    let arm = owners.arm;
    let slab = ledger_open(
        ledger,
        arm,
        "challenge_slab",
        Task8OwnerOrigin::ArmOwned,
        spans.slab.0,
        spans.slab.1,
    );
    let tables = ledger_open(
        ledger,
        arm,
        "coefficient_tables",
        Task8OwnerOrigin::ArmOwned,
        spans.tables.0,
        spans.tables.1,
    );
    open_reported_symbols(ledger, owners);
    assert_eq!(
        owners
            .coefficient_bank
            .map(|owner| (owner.base, owner.bytes)),
        Some(spans.bank),
        "Task 8 bank fill reported a span the probe did not register"
    );
    (slab, tables)
}

/// The device symbols a differential arm must name that only another arm's
/// enqueue resolved. Each arm installs them into its own probe, so a fresh
/// probe never loses an address a finished arm had already computed, and no
/// site resolves a symbol twice.
#[derive(Clone, Copy, Debug)]
struct Task8CarriedSymbols {
    eq_high: (usize, usize),
    coefficient_bank: Option<(usize, usize)>,
}

impl Task8CarriedSymbols {
    fn install(&self) {
        task8_register_symbol("ab_gkr_eq_high", self.eq_high.0, self.eq_high.1);
        if let Some((base, bytes)) = self.coefficient_bank {
            task8_register_symbol("ab_gkr_bwd_seg_coeff_bank", base, bytes);
        }
    }
}

/// The owners one arm holds open across its passes.
#[derive(Clone, Debug)]
struct Task8ArmOwners {
    arm: &'static str,
    claim_point: Task8LedgerOwner,
    claim_point_symbol: Task8LedgerOwner,
    eq_low: Task8LedgerOwner,
    eq_high: Task8LedgerOwner,
    partials: Task8LedgerOwner,
    sources: Vec<Task8LedgerOwner>,
    fold_weights: Option<Task8LedgerOwner>,
    coefficient_bank: Option<Task8LedgerOwner>,
}

#[derive(Clone, Copy, Debug)]
struct Task8ChallengeOwners {
    external: Task8LedgerOwner,
    lookup_multiplicative: Task8LedgerOwner,
    lookup_additive: Task8LedgerOwner,
    claim_batching: Task8LedgerOwner,
}

#[derive(Clone, Copy, Debug)]
struct Task8TranscriptOwners {
    seed: Task8LedgerOwner,
    claim: Task8LedgerOwner,
    prefactor: Task8LedgerOwner,
    coefficients: Task8LedgerOwner,
    challenges: Task8LedgerOwner,
}

/// Opens the two device symbols whose addresses only a production enqueue
/// argument carries, once the enqueue that used them has reported them.
fn open_reported_symbols(ledger: &mut Task8OwnerGenerationLedger, owners: &mut Task8ArmOwners) {
    let arm = owners.arm;
    let mut open = |slot: &mut Option<Task8LedgerOwner>, symbol, label| {
        if slot.is_some() {
            return;
        }
        if let Some((base, bytes)) = task8_symbol(symbol) {
            *slot = Some(ledger_open(
                ledger,
                arm,
                label,
                Task8OwnerOrigin::ArmOwned,
                base,
                bytes,
            ));
        }
    };
    open(
        &mut owners.fold_weights,
        "bwd_seg_fold_weights",
        "fold_weights_symbol",
    );
    open(
        &mut owners.coefficient_bank,
        "ab_gkr_bwd_seg_coeff_bank",
        "coefficient_bank",
    );
}

/// The bytes of an arm's Eq owners the readback observes, split into what this
/// arm's builds wrote and what the buffer already held.
fn record_eq_readback_spans(
    ledger: &Task8OwnerGenerationLedger,
    owners: &Task8ArmOwners,
    low: bool,
) -> Vec<Task8Span> {
    eq_readback_spans(ledger, if low { &owners.eq_low } else { &owners.eq_high })
}

/// Every owner one arm opens at one coordinate. `prior_publication` appears
/// only where a pass before the compared one published, and `reduced_tensor`
/// only in the window arm.
fn expected_arm_owner_labels(
    arm: &'static str,
    start_round: usize,
    sources: usize,
) -> BTreeSet<&'static str> {
    let mut labels = BTreeSet::from([
        "challenge_slab",
        "challenges",
        "claim_batching",
        "claim_point",
        "claim_point_symbol",
        "coefficient_bank",
        "coefficient_tables",
        "coefficients",
        "eq",
        "eq_high_symbol",
        "external_challenges",
        "fold_weights_symbol",
        "lookup_additive",
        "lookup_multiplicative",
        "partials",
        "publication",
        "transcript_claim",
        "transcript_prefactor",
        "transcript_seed",
    ]);
    if arm == TASK8_WINDOW_ARM {
        labels.insert("reduced_tensor");
    }
    if start_round > 3 {
        labels.insert("prior_publication");
    }
    if sources > 0 {
        labels.insert("source_backing");
    }
    labels
}

/// Opens one borrowed owner per distinct production storage backing the layer's
/// sources resolve to. The arm only reads them, and the ledger rejects any write
/// or mutation of a borrowed owner.
fn open_source_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    storage: &GpuGKRStorage<BF, E4>,
    program: &MainContinuationWindowProgram,
) -> Vec<Task8LedgerOwner> {
    let mut backings: BTreeSet<(usize, usize)> = BTreeSet::new();
    for source in &program.sources {
        let Some(place) = family_read_place(source.raw_family, source.raw_column) else {
            continue;
        };
        let address = read_place_to_gkr_address(&place);
        let resolved = resolve_storage_column(storage, address)
            .unwrap_or_else(|| panic!("Task 8 source {} address is absent", source.id.0));
        let bytes = if resolved.is_e4 {
            storage
                .get_ext_poly_for_address(address)
                .expect("Task 8 extension source lost its storage owner")
                .backing
                .len()
                * std::mem::size_of::<E4>()
        } else {
            storage
                .get_base_poly_for_address(address)
                .expect("Task 8 base source lost its storage owner")
                .backing
                .len()
                * std::mem::size_of::<BF>()
        };
        backings.insert((resolved.matrix_base as usize, bytes));
    }
    backings
        .into_iter()
        .map(|(base, bytes)| {
            ledger_open(
                ledger,
                arm,
                "source_backing",
                Task8OwnerOrigin::Borrowed(TASK8_PRODUCTION_STORAGE),
                base,
                bytes,
            )
        })
        .collect()
}

fn bind_challenge_owners_final(
    ledger: &mut Task8OwnerGenerationLedger,
    challenges: &Task8ChallengeOwners,
) {
    for owner in [
        &challenges.external,
        &challenges.lookup_multiplicative,
        &challenges.lookup_additive,
        &challenges.claim_batching,
    ] {
        ledger_bind_final(ledger, owner);
    }
}

fn bind_transcript_owners_final(
    ledger: &mut Task8OwnerGenerationLedger,
    transcript: &Task8TranscriptOwners,
) {
    for owner in [
        &transcript.seed,
        &transcript.claim,
        &transcript.prefactor,
        &transcript.coefficients,
        &transcript.challenges,
    ] {
        ledger_bind_final(ledger, owner);
    }
}

fn bind_arm_owners_final(ledger: &mut Task8OwnerGenerationLedger, owners: &Task8ArmOwners) {
    for owner in [
        &owners.claim_point,
        &owners.eq_low,
        &owners.partials,
        &owners.claim_point_symbol,
        &owners.eq_high,
    ] {
        ledger_bind_final(ledger, owner);
    }
    for owner in owners.fold_weights.iter().chain(&owners.coefficient_bank) {
        ledger_bind_final(ledger, owner);
    }
    for owner in &owners.sources {
        ledger_bind_final(ledger, owner);
    }
}

#[allow(clippy::too_many_arguments)]
fn build_prior_level(
    storage: &GpuGKRStorage<BF, E4>,
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
    target_start: usize,
    claim_point: *const E4,
    eq_low: &mut DeviceAllocation<E4>,
    partials: &mut DeviceAllocation<E4>,
    context: &ProverContext,
    ledger: &mut Task8OwnerGenerationLedger,
    probe: &Task8ProbeGuard,
    owners: &mut Task8ArmOwners,
) -> CudaResult<(Option<ContinuationPublishedLevel>, Option<Task8LedgerOwner>)> {
    let mut prior = None;
    let mut prior_owner: Option<Task8LedgerOwner> = None;
    for pass_start in (3..target_start).step_by(3) {
        launch_build_eq_high_and_low_groups_from_point(
            claim_point,
            pass_start + 3,
            folding_steps - pass_start - 3,
            owners.eq_high.base as *mut E4,
            eq_low.as_mut_ptr(),
            context,
        )?;
        ledger.absorb(owners.arm, probe);
        launch_bwd_seg_build_fold_weights(pass_start as u32, context)?;
        open_reported_symbols(ledger, owners);
        ledger.absorb(owners.arm, probe);
        let scratch = MainContinuationWindowRuntimeScratch {
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            partials_capacity: partials.len(),
        };
        let launch = match prior.as_ref() {
            None => bind_first_main_continuation_window(
                program,
                storage,
                folding_steps,
                pass_start,
                scratch,
                context,
            ),
            Some(prior) => bind_later_main_continuation_window(
                program,
                prior,
                folding_steps,
                pass_start,
                scratch,
                context,
            ),
        }
        .unwrap_or_else(|error| panic!("Task 8 prior pass {pass_start}: {error:?}"));
        let launched = launch_main_continuation_window(launch, context)?;
        let published = ledger_open_allocation(
            ledger,
            owners.arm,
            "prior_publication",
            launched.published_level().allocation(),
        );
        ledger.absorb(owners.arm, probe);
        let consumed = prior.take();
        if let Some(consumed_owner) = prior_owner.replace(published) {
            ledger_bind_final(ledger, &consumed_owner);
        }
        prior = Some(launched.into_published_level());
        drop(consumed);
    }
    Ok((prior, prior_owner))
}

#[allow(clippy::too_many_arguments)]
fn run_window_arm(
    storage: &GpuGKRStorage<BF, E4>,
    window_program: &MainContinuationWindowProgram,
    continuation_program: &gpu_gkr_compiler::ContinuationLayerProgram,
    top_bits: &[u32],
    folding_steps: usize,
    start_round: usize,
    point_host: &[E4],
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
    ledger: &mut Task8OwnerGenerationLedger,
) -> CudaResult<(ScheduledPreparedObservation, Task8CarriedSymbols)> {
    let interval_entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let probe = Task8ProbeGuard::install();
    // The one Eq-high pointer this arm resolves, registered with its own probe
    // so the launches that read the symbol without naming it can record an
    // exact range against it. No site resolves the symbol again.
    let eq_high = get_eq_high_constant_device_ptr() as usize;
    let mut carried = Task8CarriedSymbols {
        eq_high: (
            eq_high,
            GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN * size_of::<E4>(),
        ),
        coefficient_bank: None,
    };
    carried.install();
    let (mut observation, allocations) = {
        let mut allocations = Vec::new();
        let sources = open_source_owners(ledger, TASK8_WINDOW_ARM, storage, window_program);
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_point_owner =
            ledger_open_allocation(ledger, TASK8_WINDOW_ARM, "claim_point", &claim_point);
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let (claim_symbol_staging, claim_point_symbol) =
            write_claim_point_symbol(context, point_host)?;
        let claim_point_symbol_owner = ledger_open(
            ledger,
            TASK8_WINDOW_ARM,
            "claim_point_symbol",
            Task8OwnerOrigin::ArmOwned,
            claim_point_symbol,
            point_host.len() * std::mem::size_of::<E4>(),
        );
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let before_eq = context.get_device_memory_usage();
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let after_eq = context.get_device_memory_usage();
        let before_partials = after_eq;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;
        let after_partials = context.get_device_memory_usage();
        allocations.push(allocation_record_with_usage(
            "eq", &eq_low, 1, 8, 1, "best_fit", before_eq, after_eq,
        ));
        allocations.push(allocation_record_with_usage(
            "partials",
            &partials,
            1,
            8,
            1,
            "best_fit",
            before_partials,
            after_partials,
        ));
        let bank_observer = context.observe_device_memory_high_water();
        let mut bank =
            prepare_continuation_differential_bank(continuation_program, top_bits, context)?;
        let bank_report = bank_observer.finish();
        allocations.push(allocation_group_record(
            "bank",
            bank.challenge_slab().as_ptr() as usize,
            1,
            8,
            1,
            "mixed",
            2,
            &bank_report,
        ));
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let challenge_owners =
            upload_challenges(context, ledger, &probe, TASK8_WINDOW_ARM, &external_host)?;
        let (external, lookup_mul, lookup_add, batching, challenge_staging, challenge_owners) =
            challenge_owners;
        let (external_staging, lookup_mul_staging, lookup_add_staging, batching_staging) =
            challenge_staging;
        let mut owners = Task8ArmOwners {
            arm: TASK8_WINDOW_ARM,
            claim_point: claim_point_owner,
            claim_point_symbol: claim_point_symbol_owner,
            eq_low: ledger_open(
                ledger,
                TASK8_WINDOW_ARM,
                "eq",
                Task8OwnerOrigin::FactoredEq,
                eq_low.as_ptr() as usize,
                eq_low.len() * std::mem::size_of::<E4>(),
            ),
            // The one symbol lookup both Eq builds and the Eq readback of this
            // arm reuse; no site resolves the symbol again.
            eq_high: ledger_open(
                ledger,
                TASK8_WINDOW_ARM,
                "eq_high_symbol",
                Task8OwnerOrigin::FactoredEq,
                carried.eq_high.0,
                carried.eq_high.1,
            ),
            partials: ledger_open_allocation(ledger, TASK8_WINDOW_ARM, "partials", &partials),
            sources,
            fold_weights: None,
            coefficient_bank: None,
        };
        let bank_spans = bank.schedule(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        assert_eq!(bank_spans.slab.0, bank.challenge_slab().as_ptr() as usize);
        let (slab, coefficient_tables) = open_bank_owners(ledger, &mut owners, bank_spans);
        carried.coefficient_bank = Some(bank_spans.bank);
        ledger.absorb(TASK8_WINDOW_ARM, &probe);

        let before_prior = context.get_device_memory_usage();
        let prior_observer = context.observe_device_memory_high_water();
        let (prior, prior_owner) = build_prior_level(
            storage,
            window_program,
            folding_steps,
            start_round,
            claim_point.as_ptr(),
            &mut eq_low,
            &mut partials,
            context,
            ledger,
            &probe,
            &mut owners,
        )?;
        let after_prior = context.get_device_memory_usage();
        let prior_report = prior_observer.finish();
        if let Some(prior) = prior.as_ref() {
            let mut record = allocation_record_with_usage(
                "prior_publication",
                prior.allocation(),
                2,
                3,
                1,
                "best_fit",
                before_prior,
                after_prior,
            );
            record.successful_requested_bytes = prior_report.summed_requested_bytes;
            record.multiplicity = start_round / 3 - 1;
            allocations.push(record);
        }
        let prior_original = match prior_owner.as_ref() {
            None => None,
            Some(prior_owner) => {
                let first =
                    unsafe { DeviceSlice::from_raw_parts(prior_owner.base as *const E4, 1) };
                let owner = *prior_owner;
                let readback = schedule_read_device_chunked(
                    &first,
                    readback_scratch,
                    callbacks,
                    context,
                    "prior-publication-readback",
                    |offset, bytes| vec![Task8Span::read(owner.label, owner.base + offset, bytes)],
                )?;
                ledger.absorb(TASK8_WINDOW_ARM, &probe);
                Some(readback)
            }
        };
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            start_round + 3,
            folding_steps - start_round - 3,
            owners.eq_high.base as *mut E4,
            eq_low.as_mut_ptr(),
            context,
        )?;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        launch_bwd_seg_build_fold_weights(start_round as u32, context)?;
        open_reported_symbols(ledger, &mut owners);
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let scratch = MainContinuationWindowRuntimeScratch {
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            partials_capacity: partials.len(),
        };
        let before_binding = context.get_device_memory_usage();
        let binding_observer = context.observe_device_memory_high_water();
        let launch = match prior.as_ref() {
            None => bind_first_main_continuation_window(
                window_program,
                storage,
                folding_steps,
                start_round,
                scratch,
                context,
            ),
            Some(prior) => bind_later_main_continuation_window(
                window_program,
                prior,
                folding_steps,
                start_round,
                scratch,
                context,
            ),
        }
        .unwrap_or_else(|error| panic!("Task 8 window pass {start_round}: {error:?}"));
        allocations.push(Task8AllocationRecord {
            kind: "descriptor",
            owner: (&launch as *const _) as usize,
            size_bytes: std::mem::size_of_val(&launch),
            successful_requested_bytes: std::mem::size_of_val(&launch),
            physical_backing_delta_bytes: 0,
            logical_live_delta_bytes: 0,
            multiplicity: 1,
            live_from: 3,
            live_until: 4,
            overlap_group: 2,
            placement: "host_box",
            retired: true,
        });
        let launched = launch_main_continuation_window(launch, context)?;
        let after_binding = context.get_device_memory_usage();
        let binding_report = binding_observer.finish();
        let mut publication_record = allocation_record_with_usage(
            "publication",
            launched.published_level().allocation(),
            3,
            8,
            2,
            "best_fit",
            before_binding,
            after_binding,
        );
        publication_record.successful_requested_bytes = binding_report.summed_requested_bytes;
        allocations.push(publication_record);
        let publication_owner = ledger_open_allocation(
            ledger,
            TASK8_WINDOW_ARM,
            "publication",
            launched.published_level().allocation(),
        );
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let row_tiles = launched.row_tiles();
        let reduced_tensor = ledger_open(
            ledger,
            TASK8_WINDOW_ARM,
            "reduced_tensor",
            Task8OwnerOrigin::ArmOwned,
            launched.reduced_tensor() as usize,
            MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * std::mem::size_of::<E4>(),
        );
        let pre_sizes = launched.eq_sizes();
        let pre_eq = schedule_read_all_eq(
            pre_sizes,
            &eq_low,
            &owners,
            "pre-eq-readback",
            readback_scratch,
            callbacks,
            context,
            ledger,
        )?;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let mut transcript = transcript_buffers(context)?;
        let _ = &mut transcript;
        allocations.append(&mut transcript.allocations);
        let transcript_owners = open_transcript_owners(ledger, TASK8_WINDOW_ARM, &transcript);
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_active_eq_slot(&pre_sizes, eq_low.as_mut_ptr());
        let tail = WindowTailState {
            partials: partials.as_ptr(),
            row_tiles: launched.row_tiles(),
            reduced_tensor: launched.reduced_tensor(),
            prev_claim_coords: unsafe { claim_point.as_ptr().add(start_round) },
            seed: transcript.seed.as_mut_ptr(),
            claim: transcript.claim.as_mut_ptr(),
            eq_prefactor: transcript.prefactor.as_mut_ptr(),
            coeffs_out: transcript.coefficients.as_mut_ptr(),
            challenges_out: transcript.challenges.as_mut_ptr(),
            active_eq_slot_base,
            active_eq_size_before_fold,
        };
        launch_window_tensor_round_tail(WindowTailArm::Split, &tail, context)?;
        let _ = row_tiles;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let mut post_sizes = pre_sizes;
        record_active_eq_slot_fold(&mut post_sizes);
        let publication = schedule_owner_readback(
            launched.published_level().allocation(),
            &publication_owner,
            "publication-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let coefficients = schedule_owner_readback(
            &transcript.coefficients,
            &transcript_owners.coefficients,
            "coefficient-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let challenges = schedule_owner_readback(
            &transcript.challenges,
            &transcript_owners.challenges,
            "challenge-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let seed = schedule_owner_readback(
            &transcript.seed,
            &transcript_owners.seed,
            "transcript-seed-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let claim = schedule_owner_readback(
            &transcript.claim,
            &transcript_owners.claim,
            "transcript-claim-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let eq_prefactor = schedule_owner_readback(
            &transcript.prefactor,
            &transcript_owners.prefactor,
            "transcript-prefactor-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let post_eq = schedule_read_all_eq(
            post_sizes,
            &eq_low,
            &owners,
            "post-eq-readback",
            readback_scratch,
            callbacks,
            context,
            ledger,
        )?;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let boundary =
            main_continuation_post_tail_eq_boundary(start_round as u8, folding_steps, post_sizes);
        let mut live_mutations = ScheduledLiveMutationEvidence::empty();
        live_mutations.prior_original = prior_original;
        live_mutations.e4.push(schedule_live_device_mutation(
            "window-publication-lane",
            Task8LiveMutationTarget::Publication(0),
            &publication_owner,
            0,
            deterministic_e4(0x981),
            readback_scratch,
            callbacks,
            context,
        )?);
        for (index, tag) in [(0usize, 0x982), (4, 0x983), (8, 0x984)] {
            live_mutations.e4.push(schedule_live_device_mutation(
                "axis-product-infinity-coefficients",
                Task8LiveMutationTarget::Coefficient(index),
                &transcript_owners.coefficients,
                index,
                deterministic_e4(tag),
                readback_scratch,
                callbacks,
                context,
            )?);
        }
        live_mutations.e4.push(schedule_live_device_mutation(
            "row-weight",
            Task8LiveMutationTarget::Coefficient(1),
            &transcript_owners.coefficients,
            1,
            deterministic_e4(0x985),
            readback_scratch,
            callbacks,
            context,
        )?);
        for (index, tag) in [(0usize, 0x986), (1, 0x987), (2, 0x988)] {
            live_mutations.e4.push(schedule_live_device_mutation(
                "challenges",
                Task8LiveMutationTarget::Challenge(index),
                &transcript_owners.challenges,
                index,
                deterministic_e4(tag),
                readback_scratch,
                callbacks,
                context,
            )?);
        }
        live_mutations.u32.push(schedule_live_device_mutation(
            "transcript-seed",
            Task8LiveMutationTarget::Seed(0),
            &transcript_owners.seed,
            0,
            0xa5a5_5a5a,
            readback_scratch,
            callbacks,
            context,
        )?);
        live_mutations.e4.push(schedule_live_device_mutation(
            "claim",
            Task8LiveMutationTarget::Claim(0),
            &transcript_owners.claim,
            0,
            deterministic_e4(0x989),
            readback_scratch,
            callbacks,
            context,
        )?);
        live_mutations.e4.push(schedule_live_device_mutation(
            "eq-prefactor",
            Task8LiveMutationTarget::EqPrefactor(0),
            &transcript_owners.prefactor,
            0,
            deterministic_e4(0x98a),
            readback_scratch,
            callbacks,
            context,
        )?);
        live_mutations.e4.push(schedule_live_device_mutation(
            "stale-eq",
            Task8LiveMutationTarget::PostEqLow(0),
            &owners.eq_low,
            0,
            deterministic_e4(0x98b),
            readback_scratch,
            callbacks,
            context,
        )?);
        if let Some(prior_owner) = prior_owner.as_ref() {
            live_mutations.e4.push(schedule_live_device_mutation(
                "prior-publication-cell",
                Task8LiveMutationTarget::PriorPublication,
                prior_owner,
                0,
                deterministic_e4(0x98c),
                readback_scratch,
                callbacks,
                context,
            )?);
            ledger.absorb(TASK8_WINDOW_ARM, &probe);
            ledger_bind_final(ledger, prior_owner);
        }
        drop(prior);
        if let Some(bank_staging) = bank.take_bank_staging() {
            retain_in_callback(bank_staging, callbacks, context)?;
        }
        retain_in_callback(point_staging, callbacks, context)?;
        retain_in_callback(claim_symbol_staging, callbacks, context)?;
        retain_in_callback(external_staging, callbacks, context)?;
        retain_in_callback(lookup_mul_staging, callbacks, context)?;
        retain_in_callback(lookup_add_staging, callbacks, context)?;
        retain_in_callback(batching_staging, callbacks, context)?;
        retain_in_callback(transcript._seed_staging, callbacks, context)?;
        retain_in_callback(transcript._claim_staging, callbacks, context)?;
        retain_in_callback(transcript._prefactor_staging, callbacks, context)?;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        ledger_bind_final(ledger, &publication_owner);
        ledger_bind_final(ledger, &reduced_tensor);
        drop(launched);
        ledger_bind_final(ledger, &slab);
        ledger_bind_final(ledger, &coefficient_tables);
        drop(bank);
        bind_challenge_owners_final(ledger, &challenge_owners);
        drop(external);
        drop(lookup_mul);
        drop(lookup_add);
        drop(batching);
        bind_transcript_owners_final(ledger, &transcript_owners);
        drop(transcript.seed);
        drop(transcript.claim);
        drop(transcript.prefactor);
        drop(transcript.coefficients);
        drop(transcript.challenges);
        bind_arm_owners_final(ledger, &owners);
        drop(claim_point);
        drop(eq_low);
        drop(partials);
        let memory = observer.finish();
        (
            ScheduledPreparedObservation {
                publication,
                coefficients,
                challenges,
                seed,
                claim,
                eq_prefactor,
                pre_eq,
                post_eq,
                boundary: (
                    boundary.consumer_round,
                    boundary.semantic_suffix_offset,
                    boundary.eq_sizes,
                ),
                memory,
                allocations: Vec::new(),
                live_mutations,
            },
            allocations,
        )
    };
    assert!(
        probe.finish().is_empty(),
        "Task 8 window arm left an enqueue unabsorbed"
    );
    assert_eq!(observation.memory.start, interval_entry);
    assert_eq!(observation.memory.return_to_entry, interval_entry);
    observation.allocations = allocations;
    Ok((observation, carried))
}

#[allow(clippy::too_many_arguments)]
fn run_legacy_arm(
    storage: &GpuGKRStorage<BF, E4>,
    window_program: &MainContinuationWindowProgram,
    continuation_program: &gpu_gkr_compiler::ContinuationLayerProgram,
    top_bits: &[u32],
    folding_steps: usize,
    start_round: usize,
    point_host: &[E4],
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
    ledger: &mut Task8OwnerGenerationLedger,
    carried: &Task8CarriedSymbols,
) -> CudaResult<(
    ScheduledPreparedObservation,
    Vec<(SourceId, usize)>,
    ContinuationPublishedShape,
    Task8AdoptionEvidence,
)> {
    let interval_entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let probe = Task8ProbeGuard::install();
    // The window arm's probe is gone, so its Eq-high pointer and the address and
    // exact active prefix its bank fill already computed are re-registered here.
    // Neither is resolved again.
    carried.install();
    let (mut observation, source_columns, shape, adoption, allocations) = {
        let mut allocations = Vec::new();
        let sources = open_source_owners(ledger, TASK8_LEGACY_ARM, storage, window_program);
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_point_owner =
            ledger_open_allocation(ledger, TASK8_LEGACY_ARM, "claim_point", &claim_point);
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let (claim_symbol_staging, claim_point_symbol) =
            write_claim_point_symbol(context, point_host)?;
        let claim_point_symbol_owner = ledger_open(
            ledger,
            TASK8_LEGACY_ARM,
            "claim_point_symbol",
            Task8OwnerOrigin::ArmOwned,
            claim_point_symbol,
            point_host.len() * std::mem::size_of::<E4>(),
        );
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let before_eq = context.get_device_memory_usage();
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let after_eq = context.get_device_memory_usage();
        let before_partials = after_eq;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;
        let after_partials = context.get_device_memory_usage();
        allocations.push(allocation_record_with_usage(
            "eq", &eq_low, 1, 8, 1, "best_fit", before_eq, after_eq,
        ));
        allocations.push(allocation_record_with_usage(
            "partials",
            &partials,
            1,
            8,
            1,
            "best_fit",
            before_partials,
            after_partials,
        ));
        // The prior passes read the bank a previous fill left in place; this
        // arm's own fill retires that generation below.
        let borrowed_bank = (start_round > 3)
            .then(|| task8_symbol("ab_gkr_bwd_seg_coeff_bank"))
            .flatten()
            .map(|(base, bytes)| {
                ledger_open(
                    ledger,
                    TASK8_LEGACY_ARM,
                    "coefficient_bank",
                    Task8OwnerOrigin::Borrowed(TASK8_RESIDENT_COEFFICIENT_BANK),
                    base,
                    bytes,
                )
            });
        let mut owners = Task8ArmOwners {
            arm: TASK8_LEGACY_ARM,
            claim_point: claim_point_owner,
            claim_point_symbol: claim_point_symbol_owner,
            eq_low: ledger_open(
                ledger,
                TASK8_LEGACY_ARM,
                "eq",
                Task8OwnerOrigin::FactoredEq,
                eq_low.as_ptr() as usize,
                eq_low.len() * std::mem::size_of::<E4>(),
            ),
            // The one symbol lookup both Eq builds and the Eq readback of this
            // arm reuse; no site resolves the symbol again.
            eq_high: ledger_open(
                ledger,
                TASK8_LEGACY_ARM,
                "eq_high_symbol",
                Task8OwnerOrigin::FactoredEq,
                carried.eq_high.0,
                carried.eq_high.1,
            ),
            partials: ledger_open_allocation(ledger, TASK8_LEGACY_ARM, "partials", &partials),
            sources,
            fold_weights: None,
            coefficient_bank: borrowed_bank,
        };
        let before_prior = context.get_device_memory_usage();
        let prior_observer = context.observe_device_memory_high_water();
        let (prior, prior_owner) = build_prior_level(
            storage,
            window_program,
            folding_steps,
            start_round,
            claim_point.as_ptr(),
            &mut eq_low,
            &mut partials,
            context,
            ledger,
            &probe,
            &mut owners,
        )?;
        let after_prior = context.get_device_memory_usage();
        let prior_report = prior_observer.finish();
        if let Some(prior) = prior.as_ref() {
            let mut record = allocation_record_with_usage(
                "prior_publication",
                prior.allocation(),
                2,
                3,
                1,
                "best_fit",
                before_prior,
                after_prior,
            );
            record.successful_requested_bytes = prior_report.summed_requested_bytes;
            record.multiplicity = start_round / 3 - 1;
            allocations.push(record);
        }
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            start_round + 3,
            folding_steps - start_round - 3,
            owners.eq_high.base as *mut E4,
            eq_low.as_mut_ptr(),
            context,
        )?;
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let pre_sizes = make_eq_sizes(folding_steps - start_round - 3);
        let pre_eq = schedule_read_all_eq(
            pre_sizes,
            &eq_low,
            &owners,
            "pre-eq-readback",
            readback_scratch,
            callbacks,
            context,
            ledger,
        )?;
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let bank_observer = context.observe_device_memory_high_water();
        let mut rounds = prepare_continuation_differential_rounds(
            storage,
            continuation_program,
            start_round as u8,
            folding_steps,
            eq_low.as_ptr(),
            partials.as_mut_ptr(),
            prior,
            top_bits,
            context,
        )?;
        let bank_report = bank_observer.finish();
        allocations.push(allocation_group_record(
            "bank",
            rounds.challenge_slab().as_ptr() as usize,
            2,
            8,
            1,
            "mixed",
            2,
            &bank_report,
        ));
        let input_live_before = rounds.expected_input_is_live();
        let first_deltas = rounds.first_deltas().to_vec();
        let first_reads_only_published = rounds.first_reads_only_published();
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, lookup_mul, lookup_add, batching, challenge_staging, challenge_owners) =
            upload_challenges(context, ledger, &probe, TASK8_LEGACY_ARM, &external_host)?;
        let (external_staging, lookup_mul_staging, lookup_add_staging, batching_staging) =
            challenge_staging;
        let bank_spans = rounds.schedule_bank_fill(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        assert_eq!(bank_spans.slab.0, rounds.challenge_slab().as_ptr() as usize);
        if let Some(borrowed_bank) = owners.coefficient_bank.take() {
            ledger_bind_final(ledger, &borrowed_bank);
        }
        let (slab, coefficient_tables) = open_bank_owners(ledger, &mut owners, bank_spans);
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let mut transcript = transcript_buffers(context)?;
        allocations.append(&mut transcript.allocations);
        let transcript_owners = open_transcript_owners(ledger, TASK8_LEGACY_ARM, &transcript);
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let mut publications: std::collections::BTreeMap<u8, Task8LedgerOwner> =
            std::collections::BTreeMap::new();
        if let Some(prior_owner) = prior_owner.as_ref() {
            publications.insert(start_round as u8 - 3, *prior_owner);
        }
        let mut raw_publication = None;
        for local_round in 0..3 {
            let round = start_round + local_round;
            let acc_size = 1usize << (folding_steps - round - 1);
            let before_round = context.get_device_memory_usage();
            let enqueue_facts = rounds.schedule_round(round as u32, acc_size as u32, context)?;
            let after_round = context.get_device_memory_usage();
            if local_round == 0 {
                allocations.push(allocation_record_with_usage(
                    "publication",
                    rounds.live_publication(),
                    3,
                    5,
                    2,
                    "top",
                    before_round,
                    after_round,
                ));
            }
            let published = ledger_open(
                ledger,
                TASK8_LEGACY_ARM,
                "publication",
                Task8OwnerOrigin::ArmOwned,
                enqueue_facts.published.0,
                enqueue_facts.published.1,
            );
            publications.insert(round as u8, published);
            open_reported_symbols(ledger, &mut owners);
            ledger.absorb(TASK8_LEGACY_ARM, &probe);
            for depth in &enqueue_facts.retired {
                let retired = publications
                    .remove(depth)
                    .expect("Task 8 round retired a publication that was never opened");
                ledger_bind_final(ledger, &retired);
            }
            if local_round == 0 {
                let owner = publications[&(round as u8)];
                raw_publication = Some(schedule_owner_readback(
                    rounds.live_publication(),
                    &owner,
                    "publication-readback",
                    readback_scratch,
                    callbacks,
                    context,
                )?);
                ledger.absorb(TASK8_LEGACY_ARM, &probe);
            }
            let (active_eq_slot_base, active_eq_size_before_fold) = if local_round == 2 {
                resolve_active_eq_slot(&pre_sizes, eq_low.as_mut_ptr())
            } else {
                (eq_low.as_mut_ptr(), 0)
            };
            launch_backward_dual_finalize_from_partials(
                partials.as_ptr(),
                warp_partial_count(acc_size),
                unsafe { claim_point.as_ptr().add(round) },
                transcript.seed.as_mut_ptr(),
                transcript.claim.as_mut_ptr(),
                transcript.prefactor.as_mut_ptr(),
                unsafe { transcript.coefficients.as_mut_ptr().add(4 * local_round) },
                unsafe { transcript.challenges.as_mut_ptr().add(local_round) },
                active_eq_slot_base,
                active_eq_size_before_fold,
                context,
            )?;
            ledger.absorb(TASK8_LEGACY_ARM, &probe);
        }
        let mut post_sizes = pre_sizes;
        record_active_eq_slot_fold(&mut post_sizes);
        let source_columns = rounds.source_columns().to_vec();
        let shape = rounds.publication_shape();
        assert_eq!(shape.depth, start_round as u8);
        let publication = raw_publication.expect("Task 8 legacy round did not publish");
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let coefficients = schedule_owner_readback(
            &transcript.coefficients,
            &transcript_owners.coefficients,
            "coefficient-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let challenges = schedule_owner_readback(
            &transcript.challenges,
            &transcript_owners.challenges,
            "challenge-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let seed = schedule_owner_readback(
            &transcript.seed,
            &transcript_owners.seed,
            "transcript-seed-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let claim = schedule_owner_readback(
            &transcript.claim,
            &transcript_owners.claim,
            "transcript-claim-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        let eq_prefactor = schedule_owner_readback(
            &transcript.prefactor,
            &transcript_owners.prefactor,
            "transcript-prefactor-readback",
            readback_scratch,
            callbacks,
            context,
        )?;
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let post_eq = schedule_read_all_eq(
            post_sizes,
            &eq_low,
            &owners,
            "post-eq-readback",
            readback_scratch,
            callbacks,
            context,
            ledger,
        )?;
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let boundary =
            main_continuation_post_tail_eq_boundary(start_round as u8, folding_steps, post_sizes);
        let adoption = Task8AdoptionEvidence {
            had_prior: start_round > 3,
            input_live_before,
            first_deltas,
            first_reads_only_published,
            input_retired: !rounds.expected_input_is_live(),
        };
        if let Some(bank_staging) = rounds.take_bank_staging() {
            retain_in_callback(bank_staging, callbacks, context)?;
        }
        retain_in_callback(point_staging, callbacks, context)?;
        retain_in_callback(claim_symbol_staging, callbacks, context)?;
        retain_in_callback(external_staging, callbacks, context)?;
        retain_in_callback(lookup_mul_staging, callbacks, context)?;
        retain_in_callback(lookup_add_staging, callbacks, context)?;
        retain_in_callback(batching_staging, callbacks, context)?;
        retain_in_callback(transcript._seed_staging, callbacks, context)?;
        retain_in_callback(transcript._claim_staging, callbacks, context)?;
        retain_in_callback(transcript._prefactor_staging, callbacks, context)?;
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        for (_, owner) in publications.iter() {
            ledger_bind_final(ledger, owner);
        }
        ledger_bind_final(ledger, &slab);
        ledger_bind_final(ledger, &coefficient_tables);
        drop(rounds);
        bind_challenge_owners_final(ledger, &challenge_owners);
        drop(external);
        drop(lookup_mul);
        drop(lookup_add);
        drop(batching);
        bind_transcript_owners_final(ledger, &transcript_owners);
        drop(transcript.seed);
        drop(transcript.claim);
        drop(transcript.prefactor);
        drop(transcript.coefficients);
        drop(transcript.challenges);
        bind_arm_owners_final(ledger, &owners);
        drop(claim_point);
        drop(eq_low);
        drop(partials);
        let memory = observer.finish();
        (
            ScheduledPreparedObservation {
                publication,
                coefficients,
                challenges,
                seed,
                claim,
                eq_prefactor,
                pre_eq,
                post_eq,
                boundary: (
                    boundary.consumer_round,
                    boundary.semantic_suffix_offset,
                    boundary.eq_sizes,
                ),
                memory,
                allocations: Vec::new(),
                live_mutations: ScheduledLiveMutationEvidence::empty(),
            },
            source_columns,
            shape,
            adoption,
            allocations,
        )
    };
    assert!(
        probe.finish().is_empty(),
        "Task 8 legacy arm left an enqueue unabsorbed"
    );
    assert_eq!(observation.memory.start, interval_entry);
    assert_eq!(observation.memory.return_to_entry, interval_entry);
    observation.allocations = allocations;
    Ok((observation, source_columns, shape, adoption))
}

struct Task8CapacityEvidence {
    publication_bytes: usize,
    overlap_event: Task8LivePublicationEvent,
    memory: PoolMemoryHighWaterReport,
}

#[allow(clippy::too_many_arguments)]
fn run_first_pass_legacy_capacity_probe(
    storage: &GpuGKRStorage<BF, E4>,
    continuation_program: &gpu_gkr_compiler::ContinuationLayerProgram,
    top_bits: &[u32],
    folding_steps: usize,
    point_host: &[E4],
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<Task8CapacityEvidence> {
    let entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (publication_bytes, overlap_event) = {
        let (claim_point, point_staging) = upload(context, point_host)?;
        let (claim_symbol_staging, _) = write_claim_point_symbol(context, point_host)?;
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;

        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            6,
            folding_steps - 6,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        let mut rounds = prepare_continuation_differential_rounds(
            storage,
            continuation_program,
            3,
            folding_steps,
            eq_low.as_ptr(),
            partials.as_mut_ptr(),
            None,
            top_bits,
            context,
        )?;
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, external_staging) = upload(context, &external_host)?;
        let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
        let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
        let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
        let _ = rounds.schedule_bank_fill(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        let mut publication_bytes = 0usize;
        for local_round in 0..3 {
            let round = 3 + local_round;
            let acc_size = 1usize << (folding_steps - round - 1);
            let _ = rounds.schedule_round(round as u32, acc_size as u32, context)?;
            if local_round == 0 {
                publication_bytes = rounds
                    .live_publication()
                    .len()
                    .checked_mul(std::mem::size_of::<E4>())
                    .expect("Task 8 capacity publication bytes overflowed usize");
            }
        }
        let overlap_event = rounds
            .live_publication_events()
            .iter()
            .find(|event| event.round == 4)
            .cloned()
            .expect("Task 8 capacity probe did not retain the round-4 overlap event");
        assert_eq!(overlap_event.owners.len(), 2);
        assert_eq!(overlap_event.owners[0].0, 3);
        assert_eq!(overlap_event.owners[0].2, publication_bytes);
        assert_eq!(overlap_event.owners[1].0, 4);
        assert_eq!(overlap_event.owners[1].2, publication_bytes / 2);
        assert_ne!(overlap_event.owners[0].1, overlap_event.owners[1].1);
        assert_eq!(
            rounds.peak_live_publications(),
            (2, publication_bytes + publication_bytes / 2)
        );
        if let Some(bank_staging) = rounds.take_bank_staging() {
            retain_in_callback(bank_staging, callbacks, context)?;
        }
        retain_in_callback(point_staging, callbacks, context)?;
        retain_in_callback(claim_symbol_staging, callbacks, context)?;
        retain_in_callback(external_staging, callbacks, context)?;
        retain_in_callback(lookup_mul_staging, callbacks, context)?;
        retain_in_callback(lookup_add_staging, callbacks, context)?;
        retain_in_callback(batching_staging, callbacks, context)?;
        drop(rounds);
        drop(external);
        drop(lookup_mul);
        drop(lookup_add);
        drop(batching);
        drop(claim_point);
        drop(eq_low);
        drop(partials);
        (publication_bytes, overlap_event)
    };
    let memory = observer.finish();
    assert_eq!(memory.start, entry);
    assert_eq!(memory.return_to_entry, entry);
    if publication_bytes > 2usize << 30 {
        assert!(memory.physical_backing_peak_bytes > 2usize << 30);
        assert!(memory.logical_live_peak_bytes > 2usize << 30);
    }
    Ok(Task8CapacityEvidence {
        publication_bytes,
        overlap_event,
        memory,
    })
}

fn schedule_source_identity(
    storage: &GpuGKRStorage<BF, E4>,
    program: &MainContinuationWindowProgram,
    readback_scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<Vec<ScheduledSourceIdentityRecord>> {
    let mut semantic_ids = BTreeSet::new();
    let mut physical_views = std::collections::BTreeMap::new();
    let mut records = Vec::new();
    for source in &program.sources {
        assert!(semantic_ids.insert(source.id.0));
        if let Some(place) = family_read_place(source.raw_family, source.raw_column) {
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_storage_column(storage, address).unwrap_or_else(|| {
                panic!(
                    "Task 8 source {} address {address:?} is absent",
                    source.id.0
                )
            });
            let pointer = resolved.ptr as usize;
            let base = resolved.matrix_base as usize;
            assert!(pointer >= base);
            assert_eq!((pointer - base) % resolved.stride_bytes as usize, 0);
            let view = (resolved.is_e4, base, pointer - base, resolved.stride_bytes);
            if let Some(previous_address) = physical_views.insert(view, address) {
                if previous_address != address {
                    let aliases = storage
                        .layout
                        .as_ref()
                        .map(|layout| &layout.aliases)
                        .expect("shared Task 8 backing views require an artifact layout");
                    let canonical =
                        |candidate| aliases.get(&candidate).copied().unwrap_or(candidate);
                    assert_eq!(
                        canonical(previous_address),
                        canonical(address),
                        "Task 8 source {} shares an unexplained physical view",
                        source.id.0
                    );
                }
            }
            let elements = resolved.stride_bytes as usize
                / if resolved.is_e4 {
                    std::mem::size_of::<E4>()
                } else {
                    std::mem::size_of::<BF>()
                };
            assert!(elements > 0);
            let sample_indices = if elements == 1 {
                vec![0]
            } else {
                vec![0, elements - 1]
            };
            let samples = if resolved.is_e4 {
                ScheduledSourceSampleValues::Extension(
                    sample_indices
                        .into_iter()
                        .map(|index| {
                            let sample = unsafe {
                                DeviceSlice::from_raw_parts(
                                    (resolved.ptr as *const E4).add(index),
                                    1,
                                )
                            };
                            schedule_read_device_chunked(
                                sample,
                                readback_scratch,
                                callbacks,
                                context,
                                "source-identity-readback",
                                |_, _| Vec::new(),
                            )
                        })
                        .collect::<CudaResult<Vec<_>>>()?,
                )
            } else {
                ScheduledSourceSampleValues::Base(
                    sample_indices
                        .into_iter()
                        .map(|index| {
                            let sample = unsafe {
                                DeviceSlice::from_raw_parts(
                                    (resolved.ptr as *const BF).add(index),
                                    1,
                                )
                            };
                            schedule_read_device_chunked(
                                sample,
                                readback_scratch,
                                callbacks,
                                context,
                                "source-identity-readback",
                                |_, _| Vec::new(),
                            )
                        })
                        .collect::<CudaResult<Vec<_>>>()?,
                )
            };
            let backing_bytes = if resolved.is_e4 {
                storage
                    .get_ext_poly_for_address(address)
                    .expect("Task 8 extension source lost its storage owner")
                    .backing
                    .len()
                    .checked_mul(std::mem::size_of::<E4>())
                    .expect("Task 8 extension backing byte count overflowed usize")
            } else {
                storage
                    .get_base_poly_for_address(address)
                    .expect("Task 8 base source lost its storage owner")
                    .backing
                    .len()
                    .checked_mul(std::mem::size_of::<BF>())
                    .expect("Task 8 base backing byte count overflowed usize")
            };
            records.push(ScheduledSourceIdentityRecord {
                source: source.id,
                address,
                field_class: if resolved.is_e4 {
                    Task8SourceFieldClass::Extension
                } else {
                    Task8SourceFieldClass::Base
                },
                backing_base: base,
                view_offset: pointer - base,
                stride_bytes: resolved.stride_bytes as usize,
                backing_bytes,
                backing_requested_bytes: backing_bytes,
                samples,
            });
        }
    }
    assert_eq!(semantic_ids.len(), program.sources.len());
    Ok(records)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObservationMismatch {
    Publication,
    Coefficients,
    Challenges,
    Seed,
    Claim,
    EqPrefactor,
    PreEqSizes,
    PreEqLow,
    PreEqHigh,
    PostEqSizes,
    PostEqLow,
    PostEqHigh,
    Boundary,
}

fn compare_observations(
    window: &PreparedObservation,
    legacy: &PreparedObservation,
) -> Result<usize, ObservationMismatch> {
    if window.publication != legacy.publication {
        return Err(ObservationMismatch::Publication);
    }
    if window.coefficients != legacy.coefficients {
        return Err(ObservationMismatch::Coefficients);
    }
    if window.challenges != legacy.challenges {
        return Err(ObservationMismatch::Challenges);
    }
    if window.seed != legacy.seed {
        return Err(ObservationMismatch::Seed);
    }
    if window.claim != legacy.claim {
        return Err(ObservationMismatch::Claim);
    }
    if window.eq_prefactor != legacy.eq_prefactor {
        return Err(ObservationMismatch::EqPrefactor);
    }
    if window.pre_eq.sizes != legacy.pre_eq.sizes {
        return Err(ObservationMismatch::PreEqSizes);
    }
    if window.pre_eq.low != legacy.pre_eq.low {
        return Err(ObservationMismatch::PreEqLow);
    }
    if window.pre_eq.high != legacy.pre_eq.high {
        return Err(ObservationMismatch::PreEqHigh);
    }
    if window.post_eq.sizes != legacy.post_eq.sizes {
        return Err(ObservationMismatch::PostEqSizes);
    }
    if window.post_eq.low != legacy.post_eq.low {
        return Err(ObservationMismatch::PostEqLow);
    }
    if window.post_eq.high != legacy.post_eq.high {
        return Err(ObservationMismatch::PostEqHigh);
    }
    if window.boundary != legacy.boundary {
        return Err(ObservationMismatch::Boundary);
    }
    Ok(window.publication.len()
        + window.coefficients.len()
        + window.challenges.len()
        + window.seed.len()
        + window.claim.len()
        + window.eq_prefactor.len()
        + window.pre_eq.low.len()
        + window.pre_eq.high.len()
        + window.post_eq.low.len()
        + window.post_eq.high.len()
        + 3)
}

fn run_comparator_field_coverage_checks(
    window: &PreparedObservation,
    legacy: &PreparedObservation,
) -> usize {
    let mutations: Vec<(ObservationMismatch, Box<dyn Fn(&mut PreparedObservation)>)> = vec![
        (
            ObservationMismatch::Publication,
            Box::new(|value| value.publication[0] = deterministic_e4(0x901)),
        ),
        (
            ObservationMismatch::Coefficients,
            Box::new(|value| value.coefficients[0] = deterministic_e4(0x902)),
        ),
        (
            ObservationMismatch::Coefficients,
            Box::new(|value| value.coefficients[4] = deterministic_e4(0x912)),
        ),
        (
            ObservationMismatch::Coefficients,
            Box::new(|value| value.coefficients[8] = deterministic_e4(0x922)),
        ),
        (
            ObservationMismatch::Challenges,
            Box::new(|value| value.challenges[0] = deterministic_e4(0x903)),
        ),
        (
            ObservationMismatch::Challenges,
            Box::new(|value| value.challenges[1] = deterministic_e4(0x913)),
        ),
        (
            ObservationMismatch::Challenges,
            Box::new(|value| value.challenges[2] = deterministic_e4(0x923)),
        ),
        (
            ObservationMismatch::Seed,
            Box::new(|value| value.seed[0] ^= 1),
        ),
        (
            ObservationMismatch::Claim,
            Box::new(|value| value.claim[0] = deterministic_e4(0x904)),
        ),
        (
            ObservationMismatch::EqPrefactor,
            Box::new(|value| value.eq_prefactor[0] = deterministic_e4(0x905)),
        ),
        (
            ObservationMismatch::PreEqSizes,
            Box::new(|value| value.pre_eq.sizes.low ^= 1),
        ),
        (
            ObservationMismatch::PreEqLow,
            Box::new(|value| value.pre_eq.low[0] = deterministic_e4(0x906)),
        ),
        (
            ObservationMismatch::PreEqHigh,
            Box::new(|value| value.pre_eq.high[0] = deterministic_e4(0x916)),
        ),
        (
            ObservationMismatch::PostEqSizes,
            Box::new(|value| value.post_eq.sizes.low ^= 1),
        ),
        (
            ObservationMismatch::PostEqLow,
            Box::new(|value| value.post_eq.low[0] = deterministic_e4(0x917)),
        ),
        (
            ObservationMismatch::PostEqHigh,
            Box::new(|value| value.post_eq.high[0] = deterministic_e4(0x907)),
        ),
        (
            ObservationMismatch::Boundary,
            Box::new(|value| value.boundary.0 ^= 1),
        ),
    ];
    for (expected, mutate) in &mutations {
        let mut changed = window.clone();
        mutate(&mut changed);
        assert_eq!(
            compare_observations(&changed, legacy),
            Err(*expected),
            "Task 8 mutation did not reach its live semantic oracle"
        );
    }
    mutations.len()
}

fn validate_live_observation_mutations(
    window: &PreparedObservation,
    legacy: &PreparedObservation,
    mutations: ScheduledLiveMutationEvidence,
) -> (usize, BTreeSet<String>) {
    let mut checks = 0usize;
    let mut families = BTreeSet::new();
    for mutation in mutations.materialize() {
        let (family, target, e4_value, u32_value) = match mutation {
            Task8MaterializedLiveMutation::E4(family, target, value) => {
                (family, target, Some(value), None)
            }
            Task8MaterializedLiveMutation::U32(family, target, value) => {
                (family, target, None, Some(value))
            }
        };
        if matches!(target, Task8LiveMutationTarget::PriorPublication) {
            assert!(e4_value.is_some());
            families.insert(family.to_owned());
            checks += 1;
            continue;
        }
        let mut changed = window.clone();
        let expected = match target {
            Task8LiveMutationTarget::Publication(index) => {
                changed.publication[index] = e4_value.expect("E4 publication mutation");
                ObservationMismatch::Publication
            }
            Task8LiveMutationTarget::Coefficient(index) => {
                changed.coefficients[index] = e4_value.expect("E4 coefficient mutation");
                ObservationMismatch::Coefficients
            }
            Task8LiveMutationTarget::Challenge(index) => {
                changed.challenges[index] = e4_value.expect("E4 challenge mutation");
                ObservationMismatch::Challenges
            }
            Task8LiveMutationTarget::Seed(index) => {
                changed.seed[index] = u32_value.expect("u32 seed mutation");
                ObservationMismatch::Seed
            }
            Task8LiveMutationTarget::Claim(index) => {
                changed.claim[index] = e4_value.expect("E4 claim mutation");
                ObservationMismatch::Claim
            }
            Task8LiveMutationTarget::EqPrefactor(index) => {
                changed.eq_prefactor[index] = e4_value.expect("E4 Eq-prefactor mutation");
                ObservationMismatch::EqPrefactor
            }
            Task8LiveMutationTarget::PostEqLow(index) => {
                changed.post_eq.low[index] = e4_value.expect("E4 post-Eq mutation");
                ObservationMismatch::PostEqLow
            }
            Task8LiveMutationTarget::PriorPublication => unreachable!(),
        };
        assert_eq!(
            compare_observations(&changed, legacy),
            Err(expected),
            "Task 8 live {family} mutation did not reach its semantic oracle"
        );
        families.insert(family.to_owned());
        checks += 1;
    }

    let mut boundary = window.clone();
    boundary.boundary.0 ^= 1;
    assert_eq!(
        compare_observations(&boundary, legacy),
        Err(ObservationMismatch::Boundary)
    );
    assert!(families.insert("final-boundary-repoint".to_owned()));
    checks += 1;
    (checks, families)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8TopologyError {
    ProductionStorageCount,
    InvalidLifetime,
    UnretiredOwner,
    MissingAllocationEvidence,
    DuplicateRawBacking,
    OverlappingPrior,
    OverlappingOwner,
}

fn validate_single_owner_topology(
    records: &[Task8AllocationRecord],
) -> Result<(), Task8TopologyError> {
    let storage: Vec<_> = records
        .iter()
        .filter(|record| record.kind == "production_storage")
        .collect();
    if storage.len() != 1 {
        return Err(Task8TopologyError::ProductionStorageCount);
    }
    let storage = storage[0];
    for record in records {
        if record.live_from >= record.live_until
            || record.live_from < storage.live_from
            || record.live_until > storage.live_until
        {
            return Err(Task8TopologyError::InvalidLifetime);
        }
        if !record.retired && record.kind != "production_storage" {
            return Err(Task8TopologyError::UnretiredOwner);
        }
        if record.kind != "production_storage"
            && (record.size_bytes == 0 || record.successful_requested_bytes == 0)
        {
            return Err(Task8TopologyError::MissingAllocationEvidence);
        }
    }
    for (index, left) in records.iter().enumerate() {
        for right in &records[index + 1..] {
            let overlap = left.live_from < right.live_until && right.live_from < left.live_until;
            if !overlap || left.owner != right.owner {
                continue;
            }
            if left.kind == "raw_backing" && right.kind == "raw_backing" {
                return Err(Task8TopologyError::DuplicateRawBacking);
            }
            if left.kind == "prior_publication" && right.kind == "prior_publication" {
                return Err(Task8TopologyError::OverlappingPrior);
            }
            if left.kind != "production_storage" && right.kind != "production_storage" {
                return Err(Task8TopologyError::OverlappingOwner);
            }
        }
    }
    let priors: Vec<_> = records
        .iter()
        .filter(|record| record.kind == "prior_publication")
        .collect();
    for (index, left) in priors.iter().enumerate() {
        for right in &priors[index + 1..] {
            if left.live_from < right.live_until && right.live_from < left.live_until {
                return Err(Task8TopologyError::OverlappingPrior);
            }
        }
    }
    Ok(())
}

fn actual_topology_records(
    storage_owner: usize,
    sources: &[Task8SourceIdentityRecord],
    arm_records: &[Task8AllocationRecord],
) -> Vec<Task8AllocationRecord> {
    let mut records = vec![Task8AllocationRecord {
        kind: "production_storage",
        owner: storage_owner,
        size_bytes: 0,
        successful_requested_bytes: 0,
        physical_backing_delta_bytes: 0,
        logical_live_delta_bytes: 0,
        multiplicity: 1,
        live_from: 0,
        live_until: 100,
        overlap_group: 0,
        placement: "top",
        retired: true,
    }];
    let mut raw_backings = std::collections::BTreeMap::new();
    for source in sources {
        let evidence = (source.backing_bytes, source.backing_requested_bytes);
        if let Some(previous) = raw_backings.insert(source.backing_base, evidence) {
            assert_eq!(
                previous, evidence,
                "Task 8 consolidated raw backing has inconsistent size evidence"
            );
        }
    }
    records.extend(
        raw_backings
            .into_iter()
            .map(
                |(owner, (size_bytes, requested_bytes))| Task8AllocationRecord {
                    kind: "raw_backing",
                    owner,
                    size_bytes,
                    successful_requested_bytes: requested_bytes,
                    physical_backing_delta_bytes: size_bytes as i128,
                    logical_live_delta_bytes: requested_bytes as i128,
                    multiplicity: 1,
                    live_from: 0,
                    live_until: 100,
                    overlap_group: 0,
                    placement: "top",
                    retired: true,
                },
            ),
    );
    records.extend_from_slice(arm_records);
    records
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CorpusCensus {
    layouts: usize,
    layers: usize,
    coordinates: usize,
    folding_steps: Vec<usize>,
    start_rounds: Vec<usize>,
    masks: Vec<u16>,
    max_sources: usize,
    max_legacy_displacement: usize,
    publication_over_2gib: usize,
}

fn build_corpus_census() -> CorpusCensus {
    use std::collections::BTreeSet;

    use crate::backward::compile_corpus_layout;
    use crate::main_layer_execution_plan::{
        try_derive_main_layer_execution_plan, MainTailRoundBudget, LEGACY_MAIN_TAIL_MIN_ROUNDS,
    };
    use crate::{BackwardExecutionStrategy, GkrBackwardOptions};

    let mut folding_steps_seen = BTreeSet::new();
    let mut start_rounds_seen = BTreeSet::new();
    let mut masks_seen = BTreeSet::new();
    let mut layers = 0usize;
    let mut max_sources = 0usize;
    let mut max_legacy_displacement = 0usize;
    let mut publication_over_2gib = 0usize;

    for (layout, _) in crate::backward::CONTINUATION_GOLDEN_CORPUS {
        let (programs, layout_layers) = compile_corpus_layout(layout);
        let bundle = programs
            .resolve_main_continuation_window_programs()
            .expect("the retained Task 8 corpus must lower");
        let folding_steps = programs.runtime_circuit().trace_len.trailing_zeros() as usize;
        folding_steps_seen.insert(folding_steps);
        let plan = try_derive_main_layer_execution_plan(
            GkrBackwardOptions {
                windowed_r0: true,
                windowed_main_continuations: true,
                ..GkrBackwardOptions::default()
            },
            BackwardExecutionStrategy::WindowedR0,
            folding_steps,
            MainTailRoundBudget::AtLeast {
                min_tail_rounds: LEGACY_MAIN_TAIL_MIN_ROUNDS,
            },
        )
        .expect("the retained Task 8 corpus must have a continuation plan");
        let starts: Vec<_> = (0..usize::from(plan.window_count()))
            .map(|index| 3 * (index + 1))
            .collect();
        start_rounds_seen.extend(starts.iter().copied());

        assert_eq!(bundle.layers.len(), layout_layers, "{layout}");
        for (layer, program) in bundle.layers.iter().enumerate() {
            layers += 1;
            masks_seen.insert(program.shape.bits());
            max_sources = max_sources.max(program.sources.len());
            let publication_bytes = program
                .sources
                .len()
                .checked_mul(1usize << (folding_steps - 3))
                .and_then(|elements| elements.checked_mul(std::mem::size_of::<E4>()))
                .expect("Task 8 publication bytes must fit usize");
            publication_over_2gib += usize::from(publication_bytes > 2usize << 30);

            let source_program = programs.continuation_layer(layer);
            let mut seen = vec![false; source_program.coefficients.sources.len()];
            let mut displaced = 0usize;
            for (published, column) in source_program
                .binding
                .windows
                .iter()
                .flat_map(|window| &window.columns)
                .enumerate()
            {
                let source = column.source as usize;
                assert!(source < seen.len(), "{layout} layer {layer}");
                assert!(!seen[source], "{layout} layer {layer} source {source}");
                seen[source] = true;
                displaced += usize::from(published != source);
            }
            assert!(seen.into_iter().all(|seen| seen), "{layout} layer {layer}");
            max_legacy_displacement = max_legacy_displacement.max(displaced);
        }
    }

    CorpusCensus {
        layouts: crate::backward::CONTINUATION_GOLDEN_CORPUS.len(),
        layers,
        coordinates: layers,
        folding_steps: folding_steps_seen.into_iter().collect(),
        start_rounds: start_rounds_seen.into_iter().collect(),
        masks: masks_seen.into_iter().collect(),
        max_sources,
        max_legacy_displacement,
        publication_over_2gib,
    }
}

#[cfg(test)]
mod cpu_tests {
    use gpu_prover_context::{PoolMemoryHighWaterReport, PoolMemoryUsage};

    use super::super::abi::{
        MainContinuationWindowDesc as MainContinuationWindowLaunchBinding,
        MainContinuationWindowSourceRecord,
    };
    use super::super::binding::task8_window_spans;
    use super::E4;
    use super::{
        allocation_group_record, bind_arm_owners_final, bind_challenge_owners_final,
        bind_transcript_owners_final, build_corpus_census, eq_readback_spans, ledger_bind_final,
        ledger_open, signed_snapshot_delta, task8_enqueue, task8_register_symbol,
        validate_owner_generation_ledger, validate_owner_generation_structure,
        validate_single_owner_topology, BTreeSet, Task8AllocationRecord, Task8ArmOwners,
        Task8CarriedSymbols, Task8ChallengeOwners, Task8EnqueueKind, Task8LedgerError,
        Task8LedgerOwner, Task8LedgerRecord, Task8OwnerGeneration, Task8OwnerGenerationLedger,
        Task8OwnerOrigin, Task8ProbeGuard, Task8QueuedUse, Task8Span, Task8TopologyError,
        Task8TranscriptOwners, GKR_EQ_HIGH_SLOTS, MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
        TASK8_LEGACY_ARM, TASK8_PRODUCTION_STORAGE, TASK8_SHARED_DEVICE_SYMBOLS, TASK8_WINDOW_ARM,
    };
    use crate::backward::kernels::{task8_dual_finalize_spans, task8_eq_build_spans};
    use crate::backward::task8_probe::task8_register_descriptor_sources;
    use crate::backward::vm::production_bind::{
        task8_challenge_prefix_spans, task8_challenge_slot_spans,
    };
    use crate::backward::vm::seg::{task8_fold_weight_spans, task8_seg_spans};
    use crate::backward::vm::seg_coeff_eval::{
        task8_coeff_eval_reads, task8_coeff_fill_spans, SegCoeffEvalBlob, SegCoeffMonomial,
        SegCoeffRecipe, BWD_SEG_BLOB_BYTES, BWD_SEG_CHALLENGE_ABSENT,
        BWD_SEG_CHALLENGE_CLAIM_BATCHING,
    };
    use crate::backward::vm::seg_desc::{
        bwd_seg_fold_weight_run, bwd_seg_lane, BwdSegAddrSlot, BwdSegDesc,
        BWD_COEFF_ORIGIN_READ_EXT, BWD_SEG_ADDR_NONE,
    };
    use crate::backward::vm::seg_lower::{task8_lowered_seg_descriptor, Task8SegSourceSpec};
    use crate::backward::window::tail::{
        task8_tail_reduce_spans, task8_tail_round_spans, WindowTailState,
    };
    use crate::backward::{make_eq_sizes, GkrEqSizes};
    use crate::upstream::PrimeField;
    use gpu_core::primitives::field::BF;

    fn record(
        kind: &'static str,
        owner: usize,
        live_from: usize,
        live_until: usize,
    ) -> Task8AllocationRecord {
        Task8AllocationRecord {
            kind,
            owner,
            size_bytes: usize::from(kind != "production_storage"),
            successful_requested_bytes: usize::from(kind != "production_storage"),
            physical_backing_delta_bytes: 1,
            logical_live_delta_bytes: 1,
            multiplicity: 1,
            live_from,
            live_until,
            overlap_group: 0,
            placement: "test",
            retired: true,
        }
    }

    fn valid_topology() -> Vec<Task8AllocationRecord> {
        vec![
            record("production_storage", 1, 0, 20),
            record("raw_backing", 2, 0, 20),
            record("prior_publication", 3, 1, 5),
            record("publication", 4, 2, 6),
            record("prior_publication", 5, 10, 14),
            record("publication", 6, 11, 15),
        ]
    }

    #[test]
    fn cpu_main_continuation_task8_topology_rejects_duplicate_owner() {
        validate_single_owner_topology(&valid_topology()).unwrap();

        let mut duplicate_prior = valid_topology();
        duplicate_prior.push(record("prior_publication", 7, 3, 4));
        assert_eq!(
            validate_single_owner_topology(&duplicate_prior),
            Err(Task8TopologyError::OverlappingPrior)
        );

        let mut duplicate_raw = valid_topology();
        duplicate_raw.push(record("raw_backing", 2, 0, 20));
        assert_eq!(
            validate_single_owner_topology(&duplicate_raw),
            Err(Task8TopologyError::DuplicateRawBacking)
        );
    }

    #[test]
    fn cpu_main_continuation_task8_corpus_census() {
        let census = build_corpus_census();
        assert_eq!(census.layouts, 12);
        assert_eq!(census.layers, 57);
        assert_eq!(census.coordinates, 57);
        assert_eq!(census.folding_steps, [20, 22, 23, 24]);
        assert_eq!(census.start_rounds, [3, 6, 9, 12, 15, 18]);
        assert_eq!(census.masks, [0x00, 0x01, 0x03, 0x07, 0x13, 0x17, 0x1f]);
        assert_eq!(census.max_sources, 1_012);
        assert_eq!(census.max_legacy_displacement, 174);
        assert_eq!(census.publication_over_2gib, 4);
    }

    #[test]
    fn cpu_main_continuation_snapshot_decrease_is_signed_not_checked_sub() {
        assert_eq!(signed_snapshot_delta(7, 11), -4);
    }

    #[test]
    fn cpu_main_continuation_snapshot_growth_and_zero_are_preserved() {
        let raw_requested_bytes = 128usize;
        let growth_record = allocation_group_record(
            "growth",
            7,
            0,
            1,
            0,
            "test",
            1,
            &PoolMemoryHighWaterReport {
                start: PoolMemoryUsage {
                    physical_backing_bytes: 7,
                    logical_live_bytes: 11,
                },
                physical_backing_peak_bytes: 19,
                logical_live_peak_bytes: 25,
                summed_requested_bytes: raw_requested_bytes,
                peak_window_end: PoolMemoryUsage {
                    physical_backing_bytes: 31,
                    logical_live_bytes: 41,
                },
                return_to_entry: PoolMemoryUsage {
                    physical_backing_bytes: 19,
                    logical_live_bytes: 25,
                },
            },
        );
        assert_eq!(growth_record.physical_backing_delta_bytes, 12);
        assert_eq!(growth_record.logical_live_delta_bytes, 14);
        assert_eq!(growth_record.size_bytes, raw_requested_bytes);
        assert_eq!(
            growth_record.successful_requested_bytes,
            raw_requested_bytes
        );
        assert!(i128::try_from(growth_record.size_bytes).unwrap() >= 0);
        assert_eq!(signed_snapshot_delta(7, 7), 0);
    }

    const TASK8_TEST_ELEMENT: usize = 16;
    const TASK8_TEST_POINT_LEN: usize = 12;
    const TASK8_TEST_ROW_TILES: usize = 4;
    const TASK8_TEST_CHALLENGES: usize = 11;
    const TASK8_TEST_HIGH_TABLE: usize = 256;
    const TASK8_TEST_BANK_ELEMS: usize = 16;
    const TASK8_TEST_FOLD_WEIGHT_ELEMS: usize = 11;
    const TASK8_TEST_SLAB_ELEMS: usize = 10;
    const TASK8_TEST_PUBLICATION_ELEMS: usize = 128;
    const TASK8_TEST_SOURCE_BYTES: usize = 1 << 16;
    const TASK8_TEST_SOURCE_STRIDE_LOG2: u8 = 3;
    const TASK8_TEST_PUBLISH_STRIDE_LOG2: u8 = 3;
    const TASK8_TEST_SEG_ROWS: u32 = 64;
    const TASK8_TEST_ROUND: usize = 6;

    const TASK8_TEST_CLAIM_POINT: usize = 0x10_0000;
    const TASK8_TEST_CLAIM_POINT_SYMBOL: usize = 0x20_0000;
    const TASK8_TEST_EQ_LOW: usize = 0x30_0000;
    const TASK8_TEST_EQ_HIGH: usize = 0x40_0000;
    const TASK8_TEST_PARTIALS: usize = 0x50_0000;
    const TASK8_TEST_PUBLICATION: usize = 0x60_0000;
    const TASK8_TEST_SLAB: usize = 0x70_0000;
    const TASK8_TEST_TABLES: usize = 0x71_0000;
    const TASK8_TEST_BANK: usize = 0x72_0000;
    const TASK8_TEST_FOLD_WEIGHTS: usize = 0x73_0000;
    const TASK8_TEST_SOURCE: usize = 0x74_0000;
    const TASK8_TEST_CHALLENGE_BASE: usize = 0x80_0000;
    const TASK8_TEST_TRANSCRIPT_BASE: usize = 0x90_0000;
    const TASK8_TEST_REDUCED_TENSOR: usize =
        TASK8_TEST_PARTIALS + MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * TASK8_TEST_ROW_TILES * 16;

    fn task8_test_sizes() -> GkrEqSizes {
        make_eq_sizes(TASK8_TEST_CHALLENGES)
    }

    fn task8_test_slots() -> [BwdSegAddrSlot; 2] {
        [
            BwdSegAddrSlot {
                base: TASK8_TEST_SOURCE as *const u8,
                log2_stride: TASK8_TEST_SOURCE_STRIDE_LOG2,
                origin: BWD_COEFF_ORIGIN_READ_EXT,
                procedural_kind: 0,
                reserved: [0; 5],
            },
            BwdSegAddrSlot {
                base: TASK8_TEST_PUBLICATION as *const u8,
                log2_stride: TASK8_TEST_PUBLISH_STRIDE_LOG2,
                origin: BWD_COEFF_ORIGIN_READ_EXT,
                procedural_kind: 0,
                reserved: [0; 5],
            },
        ]
    }

    fn task8_test_window_descriptor() -> Box<MainContinuationWindowLaunchBinding> {
        // SAFETY: the descriptor is `repr(C)` plain data whose pointer fields
        // accept null, exactly as the production binder's zeroed box does.
        let mut desc: Box<MainContinuationWindowLaunchBinding> =
            unsafe { Box::new(std::mem::zeroed()) };
        let slots = task8_test_slots();
        desc.slot[..slots.len()].copy_from_slice(&slots);
        desc.source[0] = MainContinuationWindowSourceRecord {
            src: bwd_seg_lane(0, 0).unwrap(),
            publish: BWD_SEG_ADDR_NONE,
        };
        desc.source[1] = MainContinuationWindowSourceRecord {
            src: bwd_seg_lane(0, 1).unwrap(),
            publish: bwd_seg_lane(1, 0).unwrap(),
        };
        desc.source_count = 2;
        desc.eq_low = TASK8_TEST_EQ_LOW as *const E4;
        desc.partials = TASK8_TEST_PARTIALS as *mut E4;
        desc.row_tiles = TASK8_TEST_ROW_TILES as u32;
        desc.eq_sizes = task8_test_sizes();
        desc
    }

    /// A descriptor the lowering could emit: the class of every source is the
    /// one `assign_class` gives its origin and depth, a cache appears only where
    /// that class materializes, and the fold list is exactly those sources.
    fn task8_test_segmented_descriptor() -> Box<BwdSegDesc> {
        let slots = task8_test_slots();
        task8_lowered_seg_descriptor(
            &slots,
            &[
                // Extension backing at depth zero: `E4Direct`, publishes nothing.
                Task8SegSourceSpec {
                    extension: true,
                    delta: 0,
                    read_slot: 0,
                    read_column: 0,
                    cache_slot: 1,
                    cache_column: 0,
                },
                // Extension backing at depth three: materialized `E4Direct`,
                // so it folds and publishes into the cache slot.
                Task8SegSourceSpec {
                    extension: true,
                    delta: 3,
                    read_slot: 0,
                    read_column: 1,
                    cache_slot: 1,
                    cache_column: 0,
                },
            ],
            TASK8_TEST_SEG_ROWS,
            TASK8_TEST_EQ_LOW as *const E4,
            TASK8_TEST_PARTIALS as *mut E4,
            task8_test_sizes(),
        )
    }

    /// A blob with two live coefficients over three monomials, two of which name
    /// challenge slots.
    fn task8_test_blob() -> SegCoeffEvalBlob {
        let monomial = |challenge_idx_0: u8, challenge_idx_1: u8| SegCoeffMonomial {
            coeff: BF::from_u32_with_reduction(1),
            batch_power: 1,
            challenge_idx_0,
            challenge_idx_1,
            power_0: 1,
            power_1: 1,
            _pad: [0; 2],
        };
        SegCoeffEvalBlob {
            recipes: vec![
                SegCoeffRecipe {
                    scalar: BF::from_u32_with_reduction(1),
                    monomial_offset: 0,
                    monomial_count: 1,
                    kind: 0,
                    limb: 0,
                    _pad: [0; 2],
                },
                SegCoeffRecipe {
                    scalar: BF::from_u32_with_reduction(1),
                    monomial_offset: 1,
                    monomial_count: 2,
                    kind: 0,
                    limb: 0,
                    _pad: [0; 2],
                },
            ],
            monomials: vec![
                monomial(0, BWD_SEG_CHALLENGE_ABSENT),
                monomial(3, BWD_SEG_CHALLENGE_ABSENT),
                monomial(BWD_SEG_CHALLENGE_ABSENT, BWD_SEG_CHALLENGE_ABSENT),
            ],
        }
    }

    fn task8_test_tail_state(transcript: &Task8TranscriptOwners) -> WindowTailState {
        WindowTailState {
            partials: TASK8_TEST_PARTIALS as *const E4,
            row_tiles: TASK8_TEST_ROW_TILES,
            reduced_tensor: TASK8_TEST_REDUCED_TENSOR as *mut E4,
            prev_claim_coords: (TASK8_TEST_CLAIM_POINT + 3 * TASK8_TEST_ELEMENT) as *const E4,
            seed: transcript.seed.base as *mut u32,
            claim: transcript.claim.base as *mut E4,
            eq_prefactor: transcript.prefactor.base as *mut E4,
            coeffs_out: transcript.coefficients.base as *mut E4,
            challenges_out: transcript.challenges.base as *mut E4,
            active_eq_slot_base: TASK8_TEST_EQ_LOW as *mut E4,
            active_eq_size_before_fold: task8_test_sizes().low,
        }
    }

    fn task8_test_carried() -> Task8CarriedSymbols {
        Task8CarriedSymbols {
            eq_high: (
                TASK8_TEST_EQ_HIGH,
                GKR_EQ_HIGH_SLOTS * TASK8_TEST_HIGH_TABLE * TASK8_TEST_ELEMENT,
            ),
            coefficient_bank: Some((TASK8_TEST_BANK, TASK8_TEST_BANK_ELEMS * TASK8_TEST_ELEMENT)),
        }
    }

    fn open(
        ledger: &mut Task8OwnerGenerationLedger,
        arm: &'static str,
        label: &'static str,
        base: usize,
        bytes: usize,
    ) -> Task8LedgerOwner {
        ledger_open(ledger, arm, label, Task8OwnerOrigin::ArmOwned, base, bytes)
    }

    /// Opens one pre-enqueue scope, lets the "call" run inside it, closes it and
    /// absorbs it — the order every production call site uses.
    fn enqueue(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
        site: &'static str,
        kind: Task8EnqueueKind,
        spans: Vec<Task8Span>,
    ) {
        {
            let _scope = task8_enqueue(site, kind, || spans);
        }
        ledger.absorb(arm, probe);
    }

    fn readback(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
        site: &'static str,
        spans: Vec<Task8Span>,
    ) {
        enqueue(ledger, probe, arm, site, Task8EnqueueKind::Copy, spans);
        enqueue(
            ledger,
            probe,
            arm,
            "readback-ordering",
            Task8EnqueueKind::Callback,
            Vec::new(),
        );
    }

    fn upload(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
        label: &'static str,
        base: usize,
        bytes: usize,
    ) -> Task8LedgerOwner {
        let owner = open(ledger, arm, label, base, bytes);
        enqueue(
            ledger,
            probe,
            arm,
            "host-upload",
            Task8EnqueueKind::Copy,
            vec![Task8Span::write("upload", base, bytes)],
        );
        owner
    }

    fn live_mutation(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        owner: &Task8LedgerOwner,
        offset: usize,
    ) {
        let arm = owner.arm;
        let address = owner.base + offset * TASK8_TEST_ELEMENT;
        enqueue(
            ledger,
            probe,
            arm,
            "live-mutation",
            Task8EnqueueKind::Copy,
            vec![Task8Span::write(owner.label, address, TASK8_TEST_ELEMENT)],
        );
        readback(
            ledger,
            probe,
            arm,
            "live-mutation-readback",
            vec![Task8Span::read(owner.label, address, TASK8_TEST_ELEMENT)],
        );
        enqueue(
            ledger,
            probe,
            arm,
            "staging-retention",
            Task8EnqueueKind::Callback,
            Vec::new(),
        );
    }

    struct Task8ArmFixture {
        owners: Task8ArmOwners,
        challenges: Task8ChallengeOwners,
        transcript: Task8TranscriptOwners,
        slab: Task8LedgerOwner,
        tables: Task8LedgerOwner,
        publication: Task8LedgerOwner,
        reduced_tensor: Option<Task8LedgerOwner>,
    }

    /// Every owner an arm opens, and the uploads and slab fill that cover them,
    /// with the bank fill's spans coming from `task8_coeff_fill_spans` over the
    /// census `task8_coeff_eval_reads` derives from a real blob.
    fn open_production_arm(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
        carried: &Task8CarriedSymbols,
    ) -> Task8ArmFixture {
        let claim_point = upload(
            ledger,
            probe,
            arm,
            "claim_point",
            TASK8_TEST_CLAIM_POINT,
            TASK8_TEST_POINT_LEN * TASK8_TEST_ELEMENT,
        );
        task8_register_symbol(
            "ab_gkr_main_layer_claim_point",
            TASK8_TEST_CLAIM_POINT_SYMBOL,
            TASK8_TEST_POINT_LEN * TASK8_TEST_ELEMENT,
        );
        let claim_point_symbol = open(
            ledger,
            arm,
            "claim_point_symbol",
            TASK8_TEST_CLAIM_POINT_SYMBOL,
            TASK8_TEST_POINT_LEN * TASK8_TEST_ELEMENT,
        );
        enqueue(
            ledger,
            probe,
            arm,
            "claim-point-symbol-write",
            Task8EnqueueKind::Copy,
            vec![Task8Span::write(
                "claim_point_symbol",
                claim_point_symbol.base,
                claim_point_symbol.bytes,
            )],
        );
        let challenges = Task8ChallengeOwners {
            external: upload(
                ledger,
                probe,
                arm,
                "external_challenges",
                TASK8_TEST_CHALLENGE_BASE,
                32 * TASK8_TEST_ELEMENT,
            ),
            lookup_multiplicative: upload(
                ledger,
                probe,
                arm,
                "lookup_multiplicative",
                TASK8_TEST_CHALLENGE_BASE + 0x1000,
                TASK8_TEST_ELEMENT,
            ),
            lookup_additive: upload(
                ledger,
                probe,
                arm,
                "lookup_additive",
                TASK8_TEST_CHALLENGE_BASE + 0x2000,
                TASK8_TEST_ELEMENT,
            ),
            claim_batching: upload(
                ledger,
                probe,
                arm,
                "claim_batching",
                TASK8_TEST_CHALLENGE_BASE + 0x3000,
                TASK8_TEST_ELEMENT,
            ),
        };
        let slab = open(
            ledger,
            arm,
            "challenge_slab",
            TASK8_TEST_SLAB,
            TASK8_TEST_SLAB_ELEMS * TASK8_TEST_ELEMENT,
        );
        let tables = open(
            ledger,
            arm,
            "coefficient_tables",
            TASK8_TEST_TABLES,
            BWD_SEG_BLOB_BYTES,
        );
        let prefix = 7;
        enqueue(
            ledger,
            probe,
            arm,
            "challenge-slab-prefix-copy",
            Task8EnqueueKind::Copy,
            task8_challenge_prefix_spans(challenges.external.base, slab.base, prefix),
        );
        for (slot, source) in [
            (7usize, &challenges.lookup_multiplicative),
            (8, &challenges.lookup_additive),
            (9, &challenges.claim_batching),
        ] {
            enqueue(
                ledger,
                probe,
                arm,
                "challenge-slab-slot-copy",
                Task8EnqueueKind::Copy,
                task8_challenge_slot_spans(source.base, slab.base, slot),
            );
        }
        enqueue(
            ledger,
            probe,
            arm,
            "coefficient-table-copy",
            Task8EnqueueKind::Copy,
            vec![Task8Span::write(
                "coefficient_tables",
                tables.base,
                tables.bytes,
            )],
        );
        task8_register_symbol(
            "ab_gkr_bwd_seg_coeff_bank",
            carried.coefficient_bank.unwrap().0,
            carried.coefficient_bank.unwrap().1,
        );
        let bank = open(
            ledger,
            arm,
            "coefficient_bank",
            carried.coefficient_bank.unwrap().0,
            carried.coefficient_bank.unwrap().1,
        );
        enqueue(
            ledger,
            probe,
            arm,
            "coefficient-bank-fill",
            Task8EnqueueKind::Kernel,
            task8_coeff_fill_spans(
                &task8_coeff_eval_reads(&task8_test_blob()),
                tables.base,
                slab.base,
                bank.base,
                bank.bytes,
            ),
        );
        let owners = Task8ArmOwners {
            arm,
            claim_point,
            claim_point_symbol,
            eq_low: ledger_open(
                ledger,
                arm,
                "eq",
                Task8OwnerOrigin::FactoredEq,
                TASK8_TEST_EQ_LOW,
                TASK8_TEST_HIGH_TABLE * TASK8_TEST_ELEMENT,
            ),
            eq_high: ledger_open(
                ledger,
                arm,
                "eq_high_symbol",
                Task8OwnerOrigin::FactoredEq,
                carried.eq_high.0,
                carried.eq_high.1,
            ),
            partials: open(
                ledger,
                arm,
                "partials",
                TASK8_TEST_PARTIALS,
                MAIN_CONTINUATION_WINDOW_TENSOR_CELLS
                    * (TASK8_TEST_ROW_TILES + 1)
                    * TASK8_TEST_ELEMENT,
            ),
            sources: vec![ledger_open(
                ledger,
                arm,
                "source_backing",
                Task8OwnerOrigin::Borrowed(TASK8_PRODUCTION_STORAGE),
                TASK8_TEST_SOURCE,
                TASK8_TEST_SOURCE_BYTES,
            )],
            fold_weights: None,
            coefficient_bank: Some(bank),
        };
        let transcript = Task8TranscriptOwners {
            seed: upload(
                ledger,
                probe,
                arm,
                "transcript_seed",
                TASK8_TEST_TRANSCRIPT_BASE,
                8 * std::mem::size_of::<u32>(),
            ),
            claim: upload(
                ledger,
                probe,
                arm,
                "transcript_claim",
                TASK8_TEST_TRANSCRIPT_BASE + 0x1000,
                TASK8_TEST_ELEMENT,
            ),
            prefactor: upload(
                ledger,
                probe,
                arm,
                "transcript_prefactor",
                TASK8_TEST_TRANSCRIPT_BASE + 0x2000,
                TASK8_TEST_ELEMENT,
            ),
            coefficients: open(
                ledger,
                arm,
                "coefficients",
                TASK8_TEST_TRANSCRIPT_BASE + 0x3000,
                12 * TASK8_TEST_ELEMENT,
            ),
            challenges: open(
                ledger,
                arm,
                "challenges",
                TASK8_TEST_TRANSCRIPT_BASE + 0x4000,
                3 * TASK8_TEST_ELEMENT,
            ),
        };
        Task8ArmFixture {
            owners,
            challenges,
            transcript,
            slab,
            tables,
            publication: open(
                ledger,
                arm,
                "publication",
                TASK8_TEST_PUBLICATION,
                TASK8_TEST_PUBLICATION_ELEMS * TASK8_TEST_ELEMENT,
            ),
            reduced_tensor: None,
        }
    }

    fn replay_eq_build(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        owners: &mut Task8ArmOwners,
    ) {
        enqueue(
            ledger,
            probe,
            owners.arm,
            "eq-build",
            Task8EnqueueKind::Kernel,
            task8_eq_build_spans(
                owners.claim_point.base,
                0,
                TASK8_TEST_CHALLENGES,
                owners.eq_high.base,
                owners.eq_low.base,
            ),
        );
    }

    fn replay_fold_weights(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        owners: &mut Task8ArmOwners,
        round: usize,
    ) {
        task8_register_symbol(
            "bwd_seg_fold_weights",
            TASK8_TEST_FOLD_WEIGHTS,
            TASK8_TEST_FOLD_WEIGHT_ELEMS * TASK8_TEST_ELEMENT,
        );
        if owners.fold_weights.is_none() {
            owners.fold_weights = Some(open(
                ledger,
                owners.arm,
                "fold_weights_symbol",
                TASK8_TEST_FOLD_WEIGHTS,
                TASK8_TEST_FOLD_WEIGHT_ELEMS * TASK8_TEST_ELEMENT,
            ));
        }
        enqueue(
            ledger,
            probe,
            owners.arm,
            "fold-weight-build",
            Task8EnqueueKind::Kernel,
            task8_fold_weight_spans(round as u32, TASK8_TEST_FOLD_WEIGHTS),
        );
    }

    fn replay_eq_readback(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        owners: &Task8ArmOwners,
        site: &'static str,
    ) {
        let low = eq_readback_spans(ledger, &owners.eq_low);
        readback(ledger, probe, owners.arm, site, low);
        let high = eq_readback_spans(ledger, &owners.eq_high);
        readback(ledger, probe, owners.arm, site, high);
    }

    fn replay_readbacks(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
        transcript: &Task8TranscriptOwners,
    ) {
        for (owner, site) in [
            (&transcript.coefficients, "coefficient-readback"),
            (&transcript.challenges, "challenge-readback"),
            (&transcript.seed, "transcript-seed-readback"),
            (&transcript.claim, "transcript-claim-readback"),
            (&transcript.prefactor, "transcript-prefactor-readback"),
        ] {
            readback(
                ledger,
                probe,
                arm,
                site,
                vec![Task8Span::read(owner.label, owner.base, owner.bytes)],
            );
        }
    }

    fn replay_retentions(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
    ) {
        for _ in 0..10 {
            enqueue(
                ledger,
                probe,
                arm,
                "staging-retention",
                Task8EnqueueKind::Callback,
                Vec::new(),
            );
        }
    }

    fn finish_arm(ledger: &mut Task8OwnerGenerationLedger, fixture: &Task8ArmFixture) {
        ledger_bind_final(ledger, &fixture.publication);
        if let Some(reduced_tensor) = fixture.reduced_tensor.as_ref() {
            ledger_bind_final(ledger, reduced_tensor);
        }
        ledger_bind_final(ledger, &fixture.slab);
        ledger_bind_final(ledger, &fixture.tables);
        bind_challenge_owners_final(ledger, &fixture.challenges);
        bind_transcript_owners_final(ledger, &fixture.transcript);
        bind_arm_owners_final(ledger, &fixture.owners);
    }

    /// The window arm's stream, with every launch's spans produced by the
    /// production builders.
    fn replay_window_arm(ledger: &mut Task8OwnerGenerationLedger, arm: &'static str) {
        let probe = Task8ProbeGuard::install();
        let carried = task8_test_carried();
        carried.install();
        let mut fixture = open_production_arm(ledger, &probe, arm, &carried);
        replay_eq_build(ledger, &probe, &mut fixture.owners);
        replay_fold_weights(ledger, &probe, &mut fixture.owners, TASK8_TEST_ROUND);
        let window = task8_test_window_descriptor();
        enqueue(
            ledger,
            &probe,
            arm,
            "window-launch",
            Task8EnqueueKind::Kernel,
            task8_window_spans(&window, TASK8_TEST_ROW_TILES),
        );
        let reduced_tensor = open(
            ledger,
            arm,
            "reduced_tensor",
            TASK8_TEST_REDUCED_TENSOR,
            MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * TASK8_TEST_ELEMENT,
        );
        fixture.reduced_tensor = Some(reduced_tensor);
        replay_eq_readback(ledger, &probe, &fixture.owners, "pre-eq-readback");
        let tail = task8_test_tail_state(&fixture.transcript);
        enqueue(
            ledger,
            &probe,
            arm,
            "window-tail-reduce",
            Task8EnqueueKind::Kernel,
            task8_tail_reduce_spans(&tail),
        );
        let mut rounds = vec![Task8Span::read(
            "reduced_tensor",
            reduced_tensor.base,
            reduced_tensor.bytes,
        )];
        rounds.extend(task8_tail_round_spans(&tail));
        enqueue(
            ledger,
            &probe,
            arm,
            "window-tail-rounds",
            Task8EnqueueKind::Kernel,
            rounds,
        );
        readback(
            ledger,
            &probe,
            arm,
            "publication-readback",
            vec![Task8Span::read(
                "publication",
                fixture.publication.base,
                TASK8_TEST_ELEMENT << TASK8_TEST_PUBLISH_STRIDE_LOG2,
            )],
        );
        replay_readbacks(ledger, &probe, arm, &fixture.transcript);
        replay_eq_readback(ledger, &probe, &fixture.owners, "post-eq-readback");
        live_mutation(ledger, &probe, &fixture.publication, 0);
        for index in [0usize, 4, 8, 1] {
            live_mutation(ledger, &probe, &fixture.transcript.coefficients, index);
        }
        for index in 0..3 {
            live_mutation(ledger, &probe, &fixture.transcript.challenges, index);
        }
        live_mutation(ledger, &probe, &fixture.transcript.claim, 0);
        live_mutation(ledger, &probe, &fixture.transcript.prefactor, 0);
        live_mutation(ledger, &probe, &fixture.owners.eq_low, 0);
        replay_retentions(ledger, &probe, arm);
        finish_arm(ledger, &fixture);
        assert!(probe.finish().is_empty());
    }

    /// The legacy arm's stream: no window launch or tail, one segmented round
    /// and one fused finalize per round, all from the production builders.
    fn replay_legacy_arm(ledger: &mut Task8OwnerGenerationLedger, arm: &'static str) {
        let probe = Task8ProbeGuard::install();
        let carried = task8_test_carried();
        carried.install();
        let mut fixture = open_production_arm(ledger, &probe, arm, &carried);
        replay_eq_build(ledger, &probe, &mut fixture.owners);
        replay_eq_readback(ledger, &probe, &fixture.owners, "pre-eq-readback");
        let segmented = task8_test_segmented_descriptor();
        task8_register_descriptor_sources(&*segmented as *const BwdSegDesc as usize, 2);
        let partials = TASK8_TEST_SEG_ROWS as usize / 32;
        for local_round in 0..3usize {
            let round = TASK8_TEST_ROUND + local_round;
            replay_fold_weights(ledger, &probe, &mut fixture.owners, round);
            enqueue(
                ledger,
                &probe,
                arm,
                "segmented-round",
                Task8EnqueueKind::Kernel,
                task8_seg_spans(&segmented),
            );
            if local_round == 0 {
                readback(
                    ledger,
                    &probe,
                    arm,
                    "publication-readback",
                    vec![Task8Span::read(
                        "publication",
                        fixture.publication.base,
                        2 * TASK8_TEST_SEG_ROWS as usize * TASK8_TEST_ELEMENT,
                    )],
                );
            }
            enqueue(
                ledger,
                &probe,
                arm,
                "dual-finalize",
                Task8EnqueueKind::Kernel,
                task8_dual_finalize_spans(
                    TASK8_TEST_PARTIALS,
                    partials,
                    fixture.owners.claim_point.base + round * TASK8_TEST_ELEMENT,
                    fixture.transcript.seed.base,
                    fixture.transcript.claim.base,
                    fixture.transcript.prefactor.base,
                    fixture.transcript.coefficients.base + 4 * local_round * TASK8_TEST_ELEMENT,
                    fixture.transcript.challenges.base + local_round * TASK8_TEST_ELEMENT,
                    TASK8_TEST_EQ_LOW,
                    if local_round == 2 {
                        task8_test_sizes().low
                    } else {
                        0
                    },
                ),
            );
        }
        replay_readbacks(ledger, &probe, arm, &fixture.transcript);
        replay_eq_readback(ledger, &probe, &fixture.owners, "post-eq-readback");
        replay_retentions(ledger, &probe, arm);
        finish_arm(ledger, &fixture);
        assert!(probe.finish().is_empty());
    }

    fn replay_both_orders(
        first_arm: &'static str,
        second_arm: &'static str,
    ) -> Task8OwnerGenerationLedger {
        let mut ledger = Task8OwnerGenerationLedger::default();
        for arm in [first_arm, second_arm] {
            if arm == TASK8_WINDOW_ARM {
                replay_window_arm(&mut ledger, arm);
            } else {
                replay_legacy_arm(&mut ledger, arm);
            }
        }
        ledger
    }

    fn validate(
        ledger: &Task8OwnerGenerationLedger,
        first: &'static str,
        second: &'static str,
    ) -> usize {
        validate_owner_generation_ledger(ledger, first, second, &TASK8_SHARED_DEVICE_SYMBOLS)
    }

    /// Runs the callback's validator over evidence a mutation made malformed and
    /// reports the assertion that rejected it, or `None` if it was accepted.
    fn validator_rejection(
        ledger: &Task8OwnerGenerationLedger,
        first: &'static str,
        second: &'static str,
    ) -> Option<String> {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            validate(ledger, first, second);
        }));
        std::panic::set_hook(previous);
        outcome.err().map(|payload| {
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
                .unwrap_or_default()
        })
    }

    fn validator_rejects(
        ledger: &Task8OwnerGenerationLedger,
        first: &'static str,
        second: &'static str,
    ) -> bool {
        validator_rejection(ledger, first, second).is_some()
    }

    /// Asserts that `ledger` is a well-formed capture — the same stream the
    /// accepted ledger records, one range shorter — and that the only thing the
    /// validator objects to is the missing range.
    fn omission_rejected_by(
        ledger: &Task8OwnerGenerationLedger,
        first: &'static str,
        second: &'static str,
        invariant: &str,
    ) {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let structural = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            validate_owner_generation_structure(ledger, first, second, &TASK8_SHARED_DEVICE_SYMBOLS)
        }));
        std::panic::set_hook(previous);
        assert!(
            structural.is_ok(),
            "evidence missing {invariant:?} is otherwise a consistent capture"
        );
        rejected_by(ledger, first, second, invariant);
    }

    /// Asserts the validator rejected `ledger`, and that it did so through the
    /// invariant the mutation targets rather than an incidental defect.
    fn rejected_by(
        ledger: &Task8OwnerGenerationLedger,
        first: &'static str,
        second: &'static str,
        invariant: &str,
    ) {
        let rejection = validator_rejection(ledger, first, second)
            .unwrap_or_else(|| panic!("the validator accepted evidence missing {invariant:?}"));
        assert!(
            rejection.contains(invariant),
            "expected a rejection naming {invariant:?}, got {rejection:?}"
        );
    }

    fn arm_orders() -> [(&'static str, &'static str); 2] {
        [
            (TASK8_WINDOW_ARM, TASK8_LEGACY_ARM),
            (TASK8_LEGACY_ARM, TASK8_WINDOW_ARM),
        ]
    }

    fn slot_of(
        ledger: &Task8OwnerGenerationLedger,
        arm: &'static str,
        label: &'static str,
    ) -> usize {
        ledger
            .generations
            .iter()
            .position(|entry| entry.arm == arm && entry.label == label)
            .unwrap_or_else(|| panic!("no {label} generation for the {arm} arm"))
    }

    fn enqueue_at(ledger: &Task8OwnerGenerationLedger, site: &'static str) -> usize {
        ledger
            .enqueues
            .iter()
            .position(|enqueue| enqueue.site == site)
            .unwrap_or_else(|| panic!("no {site} enqueue"))
    }

    /// Every record one enqueue of a ledger carries.
    fn records_of(
        ledger: &Task8OwnerGenerationLedger,
        site: &'static str,
    ) -> Vec<Task8LedgerRecord> {
        let ordinal = enqueue_at(ledger, site) as u64;
        let mut records: Vec<_> = ledger
            .generations
            .iter()
            .flat_map(|entry| entry.records.iter())
            .filter(|record| record.enqueue == ordinal)
            .cloned()
            .collect();
        records.sort_by_key(|record| record.step);
        records
    }

    /// One pointer range a builder could have failed to report: the arm that
    /// enqueued it, which enqueue of that site, how the kernel used it, and the
    /// exact address and extent.
    #[derive(Clone, Copy, Debug)]
    struct Task8OmittedRange {
        arm: &'static str,
        site: &'static str,
        occurrence: usize,
        use_kind: Task8QueuedUse,
        address: usize,
        bytes: usize,
    }

    /// The ledger a capture whose builder omitted exactly `target` would have
    /// produced: the named range is gone and nothing else about the stream is,
    /// so the record census, the dense step order, the within-enqueue positions
    /// and every generation's `Final` stay internally consistent.
    fn omit_range(
        base: &Task8OwnerGenerationLedger,
        target: Task8OmittedRange,
    ) -> Task8OwnerGenerationLedger {
        let mut ledger = base.clone();
        let ordinal = ledger
            .enqueues
            .iter()
            .filter(|enqueue| enqueue.arm == target.arm && enqueue.site == target.site)
            .nth(target.occurrence)
            .unwrap_or_else(|| {
                panic!(
                    "the {} arm has no {} enqueue {}",
                    target.arm, target.site, target.occurrence
                )
            })
            .ordinal;
        let mut removed = None;
        for (slot, entry) in ledger.generations.iter_mut().enumerate() {
            if entry.arm != target.arm {
                continue;
            }
            let matches: Vec<usize> = entry
                .records
                .iter()
                .enumerate()
                .filter(|(_, record)| {
                    record.enqueue == ordinal
                        && record.use_kind == target.use_kind
                        && record.address == target.address
                        && record.range.len() == target.bytes
                })
                .map(|(index, _)| index)
                .collect();
            assert!(
                matches.len() <= 1 && (matches.is_empty() || removed.is_none()),
                "{:?} does not name exactly one recorded range",
                target
            );
            if let Some(index) = matches.first() {
                removed = Some((slot, entry.records.remove(*index)));
            }
        }
        let (slot, removed) =
            removed.unwrap_or_else(|| panic!("{:?} names no recorded range", target));
        assert_ne!(
            removed.use_kind,
            Task8QueuedUse::Write,
            "omitting a write would also have to unwind that generation's coverage"
        );
        ledger.enqueues[ordinal as usize].records -= 1;
        {
            let entry = &mut ledger.generations[slot];
            if entry.final_enqueue == Some(removed.enqueue) {
                entry.final_enqueue = Some(
                    entry
                        .last_enqueue()
                        .expect("a generation that lost a use still has one"),
                );
            }
        }
        let mut order: Vec<(u64, usize, usize)> = ledger
            .generations
            .iter()
            .enumerate()
            .flat_map(|(slot, entry)| {
                entry
                    .records
                    .iter()
                    .enumerate()
                    .map(move |(index, record)| (record.step, slot, index))
            })
            .collect();
        order.sort_by_key(|(step, _, _)| *step);
        let mut positions = vec![0usize; ledger.enqueues.len()];
        for (step, (_, slot, index)) in order.into_iter().enumerate() {
            let record = &mut ledger.generations[slot].records[index];
            record.step = step as u64;
            let position = &mut positions[record.enqueue as usize];
            record.position = *position;
            *position += 1;
        }
        ledger.next_step = positions.iter().sum::<usize>() as u64;
        ledger
    }

    #[test]
    fn cpu_main_continuation_owner_generation_accepts_both_real_arm_orders() {
        let sizes = task8_test_sizes();
        for (first_arm, second_arm) in arm_orders() {
            let ledger = replay_both_orders(first_arm, second_arm);
            assert_eq!(
                validate(&ledger, first_arm, second_arm),
                TASK8_SHARED_DEVICE_SYMBOLS.len()
            );
            for arm in [first_arm, second_arm] {
                assert!(ledger.resident_reads(arm) > 0);
            }
            let window = ledger.enqueue_sites(TASK8_WINDOW_ARM);
            let legacy = ledger.enqueue_sites(TASK8_LEGACY_ARM);
            assert_eq!(window["window-launch"], 1);
            assert_eq!(window["window-tail-reduce"], 1);
            assert_eq!(window["window-tail-rounds"], 1);
            assert_eq!(window["fold-weight-build"], 1);
            assert!(!legacy.contains_key("window-launch"));
            assert_eq!(legacy["segmented-round"], 3);
            assert_eq!(legacy["dual-finalize"], 3);
            assert_eq!(legacy["fold-weight-build"], 3);
            for sites in [&window, &legacy] {
                assert_eq!(sites["coefficient-bank-fill"], 1);
                assert_eq!(sites["challenge-slab-slot-copy"], 3);
                assert_eq!(sites["claim-point-symbol-write"], 1);
            }

            // The production census, as the validated ledger recorded it.
            let element = TASK8_TEST_ELEMENT;
            let claim = records_of(&ledger, "fold-weight-build");
            let claim_read = claim
                .iter()
                .find(|record| record.role == "ab_gkr_main_layer_claim_point")
                .expect("the fold-weight build reads the claim point");
            assert_eq!(
                claim_read.range.len(),
                3 * element,
                "the fold-weight build reads only the three coordinates below its round"
            );
            assert_eq!(
                claim_read.address,
                TASK8_TEST_CLAIM_POINT_SYMBOL + (TASK8_TEST_ROUND - 3) * element
            );
            let launch = records_of(&ledger, "window-launch");
            let d3 = bwd_seg_fold_weight_run(3);
            let weights: Vec<_> = launch
                .iter()
                .filter(|record| record.role == "bwd_seg_fold_weights")
                .collect();
            assert_eq!(weights.len(), 1, "a window folds at depth three only");
            assert_eq!(
                weights[0].address,
                TASK8_TEST_FOLD_WEIGHTS + d3.start * element
            );
            assert_eq!(weights[0].range.len(), (d3.end - d3.start) * element);
            let published: Vec<_> = launch
                .iter()
                .filter(|record| record.role == "published_column")
                .collect();
            assert_eq!(published.len(), 2);
            assert_eq!(published[0].use_kind, Task8QueuedUse::Write);
            assert_eq!(published[1].use_kind, Task8QueuedUse::Read);
            assert_eq!(published[0].range, published[1].range);
            assert_eq!(
                launch
                    .iter()
                    .find(|record| record.role == "eq_low")
                    .unwrap()
                    .range
                    .len(),
                (1usize << sizes.low) * element
            );
            let round = records_of(&ledger, "segmented-round");
            let seg_weights: Vec<_> = round
                .iter()
                .filter(|record| record.role == "bwd_seg_fold_weights")
                .map(|record| record.address)
                .collect();
            for delta in [0u8, 3] {
                let run = bwd_seg_fold_weight_run(delta);
                let named = seg_weights.contains(&(TASK8_TEST_FOLD_WEIGHTS + run.start * element));
                assert_eq!(
                    named,
                    delta == 3,
                    "only the runs the live source deltas name are read"
                );
            }
            assert!(
                !seg_weights.contains(
                    &(TASK8_TEST_FOLD_WEIGHTS + bwd_seg_fold_weight_run(2).start * element)
                ),
                "no live source folds at depth two"
            );
            let cached: Vec<_> = round
                .iter()
                .filter(|record| record.role == "published_column")
                .collect();
            assert_eq!(cached.len(), 2);
            assert_eq!(cached[0].use_kind, Task8QueuedUse::Write);
            assert_eq!(cached[1].use_kind, Task8QueuedUse::Read);

            // The coefficient fill records exactly the live recipe and monomial
            // records and the challenge slots those monomials name.
            let reads = task8_coeff_eval_reads(&task8_test_blob());
            assert_eq!(reads.challenge_slots, vec![0, 3, 9]);
            let fill = records_of(&ledger, "coefficient-bank-fill");
            let tables: Vec<_> = fill
                .iter()
                .filter(|record| record.role == "coefficient_tables")
                .map(|record| {
                    record.range.start - TASK8_TEST_TABLES..record.range.end - TASK8_TEST_TABLES
                })
                .collect();
            assert_eq!(tables, reads.table_ranges);
            assert!(
                tables.iter().map(|range| range.len()).sum::<usize>() < BWD_SEG_BLOB_BYTES,
                "the fill reads its live records, not the whole staged blob"
            );
            let slots: Vec<_> = fill
                .iter()
                .filter(|record| record.role == "challenge_slab")
                .map(|record| (record.address - TASK8_TEST_SLAB) / element)
                .collect();
            assert_eq!(slots, reads.challenge_slots);
        }
    }

    #[test]
    fn cpu_main_continuation_owner_generation_validator_rejects_stale_generation_two_reads() {
        for (first_arm, second_arm) in arm_orders() {
            let base = replay_both_orders(first_arm, second_arm);
            assert_eq!(
                validate(&base, first_arm, second_arm),
                TASK8_SHARED_DEVICE_SYMBOLS.len()
            );

            // Generation two reads the shared symbol before its own write covers
            // it: the successor inherits nothing from the retired arm.
            let mut stale = base.clone();
            {
                let slot = slot_of(&stale, second_arm, "claim_point_symbol");
                let entry = &mut stale.generations[slot];
                let write = entry
                    .records
                    .iter()
                    .position(|record| record.use_kind == Task8QueuedUse::Write)
                    .unwrap();
                entry.records.remove(write);
            }
            assert!(validator_rejects(&stale, first_arm, second_arm));

            // A use of the retired arm's generation after its `Final`.
            let mut retired = base.clone();
            {
                let slot = slot_of(&retired, first_arm, "claim_point_symbol");
                let last = retired.generations[slot].records.last().unwrap().clone();
                let successor = slot_of(&retired, second_arm, "claim_point_symbol");
                let after = retired.generations[successor]
                    .records
                    .last()
                    .unwrap()
                    .clone();
                let entry = &mut retired.generations[slot];
                entry.records.push(Task8LedgerRecord {
                    step: after.step + 1,
                    enqueue: after.enqueue,
                    position: after.position + 1,
                    ..last
                });
            }
            assert!(validator_rejects(&retired, first_arm, second_arm));
        }
    }

    #[test]
    fn cpu_main_continuation_owner_generation_validator_rejects_tokens_opened_after_their_call() {
        for (first_arm, second_arm) in arm_orders() {
            let base = replay_both_orders(first_arm, second_arm);
            assert_eq!(
                validate(&base, first_arm, second_arm),
                TASK8_SHARED_DEVICE_SYMBOLS.len()
            );

            let mut late = base.clone();
            {
                let index = enqueue_at(&late, "eq-build");
                late.enqueues[index].issued_at_open += 1;
            }
            assert!(validator_rejects(&late, first_arm, second_arm));

            let mut wide = base.clone();
            {
                let index = enqueue_at(&wide, "coefficient-bank-fill");
                wide.enqueues[index].issued_at_close += 1;
            }
            assert!(validator_rejects(&wide, first_arm, second_arm));

            // The Eq build's token now sits after the launch that reads what it
            // writes, which is what moving a real-call token after its call
            // produces in the recorded stream.
            let mut moved = base.clone();
            {
                let build = enqueue_at(&moved, "eq-build") as u64;
                let reader = enqueue_at(&moved, "fold-weight-build") as u64;
                for entry in &mut moved.generations {
                    for record in &mut entry.records {
                        if record.enqueue == build {
                            record.enqueue = reader;
                            record.step += 1_000_000;
                        }
                    }
                    entry.records.sort_by_key(|record| record.step);
                }
            }
            assert!(validator_rejects(&moved, first_arm, second_arm));
        }
    }

    #[test]
    fn cpu_main_continuation_owner_generation_validator_rejects_census_and_overlap_mutations() {
        for (first_arm, second_arm) in arm_orders() {
            let base = replay_both_orders(first_arm, second_arm);
            assert_eq!(
                validate(&base, first_arm, second_arm),
                TASK8_SHARED_DEVICE_SYMBOLS.len(),
                "the ledger every mutation below starts from is accepted"
            );
            let mut families = BTreeSet::new();
            let element = TASK8_TEST_ELEMENT;
            let reads = task8_coeff_eval_reads(&task8_test_blob());

            // Each mutation below removes exactly one range a production builder
            // reported, named by arm, enqueue, use and extent, and leaves a
            // ledger whose census, steps, positions and `Final` bindings are the
            // ones that capture would have carried.

            // The claim-point coordinates the fold-weight build reads.
            for arm in [first_arm, second_arm] {
                let missing_claim = omit_range(
                    &base,
                    Task8OmittedRange {
                        arm,
                        site: "fold-weight-build",
                        occurrence: 0,
                        use_kind: Task8QueuedUse::Read,
                        address: TASK8_TEST_CLAIM_POINT_SYMBOL + (TASK8_TEST_ROUND - 3) * element,
                        bytes: 3 * element,
                    },
                );
                omission_rejected_by(
                    &missing_claim,
                    first_arm,
                    second_arm,
                    "a fold-weight build reads the claim point exactly once",
                );
            }
            families.insert("missing-claim-point-range");

            // The fold-weight run each folding launch reads, in the arm that
            // enqueues that launch.
            let d3 = bwd_seg_fold_weight_run(3);
            for (arm, site) in [
                (TASK8_WINDOW_ARM, "window-launch"),
                (TASK8_LEGACY_ARM, "segmented-round"),
            ] {
                let missing_run = omit_range(
                    &base,
                    Task8OmittedRange {
                        arm,
                        site,
                        occurrence: 0,
                        use_kind: Task8QueuedUse::Read,
                        address: TASK8_TEST_FOLD_WEIGHTS + d3.start * element,
                        bytes: (d3.end - d3.start) * element,
                    },
                );
                omission_rejected_by(
                    &missing_run,
                    first_arm,
                    second_arm,
                    "a folding launch reads the fold-weight runs its deltas name",
                );
            }
            families.insert("missing-fold-weight-run");

            // Either half of the coefficient fill's staged-table census: the
            // live recipe records, or the monomials those recipes reference.
            assert_eq!(
                reads.table_ranges.len(),
                2,
                "the fill's census names the recipe section and the monomial section"
            );
            for (index, range) in reads.table_ranges.iter().enumerate() {
                let missing_tables = omit_range(
                    &base,
                    Task8OmittedRange {
                        arm: first_arm,
                        site: "coefficient-bank-fill",
                        occurrence: 0,
                        use_kind: Task8QueuedUse::Read,
                        address: TASK8_TEST_TABLES + range.start,
                        bytes: range.len(),
                    },
                );
                omission_rejected_by(
                    &missing_tables,
                    first_arm,
                    second_arm,
                    if index == 0 {
                        "a coefficient fill reads its live recipe records"
                    } else {
                        "a coefficient fill reads the monomials its recipes reference"
                    },
                );
            }
            families.insert("missing-coefficient-record");

            // The batching slot every monomial in that fill scales by.
            let missing_challenge = omit_range(
                &base,
                Task8OmittedRange {
                    arm: first_arm,
                    site: "coefficient-bank-fill",
                    occurrence: 0,
                    use_kind: Task8QueuedUse::Read,
                    address: TASK8_TEST_SLAB + BWD_SEG_CHALLENGE_CLAIM_BATCHING as usize * element,
                    bytes: element,
                },
            );
            omission_rejected_by(
                &missing_challenge,
                first_arm,
                second_arm,
                "a coefficient fill reads the batching slot every monomial scales by",
            );
            families.insert("missing-challenge-slot");

            // The published column's read moved before the write that covers it.
            let mut reordered = base.clone();
            {
                let slot = slot_of(&reordered, first_arm, "publication");
                let entry = &mut reordered.generations[slot];
                let first = entry
                    .records
                    .iter()
                    .position(|record| record.role == "published_column")
                    .unwrap();
                let steps = (entry.records[first].step, entry.records[first + 1].step);
                entry.records[first].step = steps.1;
                entry.records[first + 1].step = steps.0;
                entry.records.swap(first, first + 1);
            }
            assert!(validator_rejects(&reordered, first_arm, second_arm));
            families.insert("published-read-before-write");

            let mut partial = base.clone();
            {
                let slot = slot_of(&partial, first_arm, "coefficients");
                let entry = &mut partial.generations[slot];
                let record = entry
                    .records
                    .iter_mut()
                    .find(|record| record.use_kind == Task8QueuedUse::Write)
                    .unwrap();
                record.range.end -= TASK8_TEST_ELEMENT;
            }
            assert!(validator_rejects(&partial, first_arm, second_arm));
            families.insert("partial-initialization");

            let mut early_final = base.clone();
            {
                let slot = slot_of(&early_final, first_arm, "claim_point");
                let entry = &mut early_final.generations[slot];
                entry.final_enqueue = Some(entry.records[0].enqueue);
            }
            assert!(validator_rejects(&early_final, first_arm, second_arm));
            families.insert("final-before-last-use");

            let mut unbound = base.clone();
            {
                let slot = slot_of(&unbound, first_arm, "partials");
                unbound.generations[slot].final_enqueue = None;
            }
            assert!(validator_rejects(&unbound, first_arm, second_arm));
            families.insert("unbound-final");

            let mut repeated = base.clone();
            {
                let slot = slot_of(&repeated, first_arm, "claim_point_symbol");
                repeated.generations[slot].superseded_by = None;
            }
            assert!(validator_rejects(&repeated, first_arm, second_arm));
            families.insert("repeated-address-without-retirement");

            let mut borrowed = base.clone();
            {
                let slot = slot_of(&borrowed, first_arm, "source_backing");
                borrowed.generations[slot].records[0].use_kind = Task8QueuedUse::Write;
            }
            assert!(validator_rejects(&borrowed, first_arm, second_arm));
            families.insert("write-to-borrowed-storage");

            let mut resident = base.clone();
            {
                let slot = slot_of(&resident, first_arm, "partials");
                resident.generations[slot].records[0].use_kind = Task8QueuedUse::ResidentRead;
            }
            assert!(validator_rejects(&resident, first_arm, second_arm));
            families.insert("resident-read-outside-eq");

            // The reduced tensor lives inside the partial buffer. Rebinding the
            // one range that overlaps to the still-live allocation is the only
            // difference between this ledger and the accepted one above.
            rejected_by(
                &rebind_reduced_tensor_write(&base),
                first_arm,
                second_arm,
                "used bytes its generation had not covered",
            );
            families.insert("finalized-narrow-overlap");
            // A direct `owner_of` observation, not a validator verdict: the
            // retired sub-buffer's address binds to a successor generation once
            // one exists, and to nothing before that.
            assert_eq!(overlap_successor_owner(first_arm), "reduced_tensor");

            assert_eq!(families.len(), 12);
        }
    }

    /// The accepted two-arm ledger with exactly one range rebound: the tail
    /// reduction's write of the reduced tensor is attributed to the partial
    /// buffer that tensor lives inside. Arm order, enqueue census, dense steps,
    /// within-enqueue positions and every generation's `Final` are the ones the
    /// accepted ledger carries.
    fn rebind_reduced_tensor_write(
        base: &Task8OwnerGenerationLedger,
    ) -> Task8OwnerGenerationLedger {
        let mut ledger = base.clone();
        let tensor = slot_of(&ledger, TASK8_WINDOW_ARM, "reduced_tensor");
        let partials = slot_of(&ledger, TASK8_WINDOW_ARM, "partials");
        let position = ledger.generations[tensor]
            .records
            .iter()
            .position(|record| {
                record.site == "window-tail-reduce" && record.use_kind == Task8QueuedUse::Write
            })
            .expect("the tail reduction writes the reduced tensor");
        let moved = ledger.generations[tensor].records.remove(position);
        assert_eq!(
            ledger.generations[tensor].final_enqueue,
            ledger.generations[tensor].last_enqueue(),
            "the tensor's Final still names its own last use"
        );
        let entry = &mut ledger.generations[tensor];
        let mut coverage = Vec::new();
        for record in &entry.records {
            if record.use_kind == Task8QueuedUse::Write {
                Task8OwnerGeneration::absorb(&mut coverage, record.range.clone());
            }
        }
        entry.initialized = coverage;
        Task8OwnerGeneration::absorb(
            &mut ledger.generations[partials].initialized,
            moved.range.clone(),
        );
        let entry = &mut ledger.generations[partials];
        entry.records.push(moved);
        entry.records.sort_by_key(|record| record.step);
        assert_eq!(
            entry.final_enqueue,
            entry.last_enqueue(),
            "the allocation's Final still names its own last use"
        );
        ledger
    }

    /// The owner a span inside a finalized reduced tensor binds to once an
    /// explicit successor generation takes that address back.
    fn overlap_successor_owner(arm: &'static str) -> &'static str {
        let mut ledger = Task8OwnerGenerationLedger::default();
        replay_window_arm(&mut ledger, arm);
        let tensor = slot_of(&ledger, arm, "reduced_tensor");
        let (base, bytes) = {
            let entry = &ledger.generations[tensor];
            (entry.owner, entry.covered.end - entry.covered.start)
        };
        assert_eq!(
            ledger.owner_of(&(base..base + bytes)),
            Err(Task8LedgerError::UseAfterFinal),
            "a finalized sub-buffer must not fall back to the allocation it lives in"
        );
        let successor = ledger
            .open(
                TASK8_LEGACY_ARM,
                "reduced_tensor",
                Task8OwnerOrigin::ArmOwned,
                base,
                bytes,
            )
            .expect("the retired sub-buffer admits a successor");
        assert_eq!(ledger.owner_of(&(base..base + bytes)), Ok(successor.slot));
        ledger.generations[successor.slot].label
    }

    #[test]
    fn cpu_main_continuation_owner_generation_requires_carried_symbol_state() {
        let window = task8_test_window_descriptor();
        let segmented = task8_test_segmented_descriptor();
        let carried = task8_test_carried();

        // A fresh probe holds nothing a finished arm resolved, so neither
        // builder can record its reads.
        for builder in 0..2 {
            let probe = Task8ProbeGuard::install();
            task8_register_descriptor_sources(&*segmented as *const BwdSegDesc as usize, 2);
            assert!(
                probe_spans(&probe, builder, &window, &segmented).is_none(),
                "a fresh probe must not invent a device symbol"
            );
        }

        // Eq-high alone is not enough for either builder: both read the bank.
        for builder in 0..2 {
            let probe = Task8ProbeGuard::install();
            task8_register_symbol("ab_gkr_eq_high", carried.eq_high.0, carried.eq_high.1);
            task8_register_symbol(
                "bwd_seg_fold_weights",
                TASK8_TEST_FOLD_WEIGHTS,
                TASK8_TEST_FOLD_WEIGHT_ELEMS * TASK8_TEST_ELEMENT,
            );
            task8_register_descriptor_sources(&*segmented as *const BwdSegDesc as usize, 2);
            assert!(
                probe_spans(&probe, builder, &window, &segmented).is_none(),
                "a later-start arm must not invent a coefficient bank"
            );
        }

        // The carried address and exact active prefix resolve both builders, and
        // both arm orders then validate.
        for builder in 0..2 {
            let probe = Task8ProbeGuard::install();
            carried.install();
            task8_register_symbol(
                "bwd_seg_fold_weights",
                TASK8_TEST_FOLD_WEIGHTS,
                TASK8_TEST_FOLD_WEIGHT_ELEMS * TASK8_TEST_ELEMENT,
            );
            task8_register_descriptor_sources(&*segmented as *const BwdSegDesc as usize, 2);
            let spans = probe_spans(&probe, builder, &window, &segmented)
                .expect("the carried symbols resolve the builder");
            assert_eq!(
                spans
                    .iter()
                    .find(|span| span.role == "ab_gkr_bwd_seg_coeff_bank")
                    .unwrap()
                    .bytes,
                carried.coefficient_bank.unwrap().1,
                "the bank read is the prefix the fill wrote"
            );
            assert!(spans
                .iter()
                .any(|span| span.role == "ab_gkr_eq_high" && span.address == carried.eq_high.0));
        }

        for (first_arm, second_arm) in arm_orders() {
            let ledger = replay_both_orders(first_arm, second_arm);
            assert_eq!(
                validate(&ledger, first_arm, second_arm),
                TASK8_SHARED_DEVICE_SYMBOLS.len()
            );
        }
    }

    /// Opens one scope around a production span builder and returns the spans
    /// the probe resolved, or reports that it could not resolve them.
    fn probe_spans(
        probe: &Task8ProbeGuard,
        builder: usize,
        window: &MainContinuationWindowLaunchBinding,
        segmented: &BwdSegDesc,
    ) -> Option<Vec<Task8Span>> {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if builder == 0 {
                let _scope = task8_enqueue("window-launch", Task8EnqueueKind::Kernel, || {
                    task8_window_spans(window, TASK8_TEST_ROW_TILES)
                });
            } else {
                let _scope = task8_enqueue("segmented-round", Task8EnqueueKind::Kernel, || {
                    task8_seg_spans(segmented)
                });
            }
        }));
        std::panic::set_hook(previous);
        outcome.ok()?;
        Some(probe.drain().pop()?.spans)
    }
}

struct Task8DifferentialAccumulator {
    layers: usize,
    coordinates: usize,
    folding_steps: BTreeSet<usize>,
    start_rounds: BTreeSet<usize>,
    masks: BTreeSet<u16>,
    max_sources: usize,
    max_legacy_displacement: usize,
    semantic_comparisons: usize,
    publication_elements_compared: usize,
    comparator_field_coverage_checks: usize,
    mutation_checks: usize,
    source_table_identity_rows: usize,
    source_identity_records: usize,
    source_id_census: std::collections::BTreeMap<usize, Vec<u32>>,
    source_backing_census: std::collections::BTreeMap<usize, usize>,
    allocation_records: usize,
    topology_owner_records: usize,
    topology_owner_kinds: BTreeSet<String>,
    topology_coordinates: usize,
    later_start_shared_prior_coordinates: usize,
    multi_source_coordinates: usize,
    arm_memory_comparisons: usize,
    procedural_source_records: usize,
    mutation_families: BTreeSet<String>,
    capacity_overlap_rows: usize,
    capacity_heavy_layers: Vec<usize>,
    capacity_publication_bytes: Vec<usize>,
    capacity_overlap_live_bytes: Vec<usize>,
    capacity_overlap_owner_counts: Vec<usize>,
    capacity_physical_peak_bytes: Vec<usize>,
    capacity_logical_peak_bytes: Vec<usize>,
    ledger_coordinates: usize,
    ledger_owner_generations: usize,
    ledger_shared_symbol_transitions: usize,
    ledger_enqueue_pointer_records: usize,
    ledger_owner_records: usize,
}

const TASK8_MUTATION_FAMILIES: [&str; 16] = [
    "axis-product-infinity-coefficients",
    "challenges",
    "claim",
    "duplicate-missing-canonical-map",
    "duplicate-raw-owner",
    "eq-prefactor",
    "final-boundary-repoint",
    "overlapping-prior-owner",
    "prior-publication-cell",
    "row-weight",
    "seeded-adoption-delta-3",
    "source-column-displacement",
    "stale-eq",
    "transcript-seed",
    "window-publication-lane",
    "zero-remainder-take",
];

fn assert_source_records_nonvacuous(records: &[Task8SourceIdentityRecord], expected: usize) {
    assert_eq!(records.len(), expected);
    let mut source_ids = BTreeSet::new();
    let mut nonzero = 0usize;
    for record in records {
        assert!(source_ids.insert(record.source.0));
        match &record.samples {
            Task8SourceSampleValues::Base(values) => {
                assert!(!values.is_empty());
                nonzero += usize::from(values.iter().any(|value| !value.is_zero()));
            }
            Task8SourceSampleValues::Extension(values) => {
                assert!(!values.is_empty());
                nonzero += usize::from(values.iter().any(|value| !value.is_zero()));
            }
        }
    }
    if !records.is_empty() {
        assert!(
            nonzero > 0,
            "Task 8 production source samples were all zero"
        );
        assert!(
            records.len() == 1
                || records.iter().enumerate().any(|(index, left)| {
                    records[index + 1..]
                        .iter()
                        .any(|right| left.source != right.source && left.samples != right.samples)
                }),
            "Task 8 retained no distinct sampled tuples across semantic SourceIds"
        );
    }
}

struct Task8TopologyEvidence {
    mutation_checks: usize,
    owner_records: usize,
    owner_kinds: BTreeSet<String>,
}

fn validate_actual_topology_mutations(
    storage_owner: usize,
    sources: &[Task8SourceIdentityRecord],
    arm_records: &[Task8AllocationRecord],
) -> Task8TopologyEvidence {
    let records = actual_topology_records(storage_owner, sources, arm_records);
    validate_single_owner_topology(&records).expect("Task 8 live allocation topology is invalid");
    let owner_records = records.len();
    let owner_kinds = records
        .iter()
        .map(|record| record.kind.to_owned())
        .collect();
    let raw = records
        .iter()
        .find(|record| record.kind == "raw_backing")
        .cloned()
        .expect("Task 8 live topology retained no raw backing");
    let mut duplicate_raw = records.clone();
    duplicate_raw.push(raw);
    assert_eq!(
        validate_single_owner_topology(&duplicate_raw),
        Err(Task8TopologyError::DuplicateRawBacking)
    );
    let mut checks = 1usize;
    if let Some(prior) = records
        .iter()
        .find(|record| record.kind == "prior_publication")
        .cloned()
    {
        let mut duplicate_prior = records;
        let mut second = prior;
        second.owner ^= 1usize << (usize::BITS - 2);
        duplicate_prior.push(second);
        assert_eq!(
            validate_single_owner_topology(&duplicate_prior),
            Err(Task8TopologyError::OverlappingPrior)
        );
        checks += 1;
    }
    Task8TopologyEvidence {
        mutation_checks: checks,
        owner_records,
        owner_kinds,
    }
}

#[inline(never)]
pub(crate) fn schedule_prepared_main_continuation_differential(
    request: Task8ContinuationDifferentialRequest,
    storage: &GpuGKRStorage<BF, E4>,
    programs: &GkrPrograms,
    inits_and_teardowns_top_bits: &[u32],
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    let folding_steps = programs.runtime_circuit().trace_len.trailing_zeros() as usize;
    let plan = crate::main_continuation_window_count(
        GkrBackwardOptions {
            windowed_r0: true,
            windowed_main_continuations: true,
            ..GkrBackwardOptions::default()
        },
        BackwardExecutionStrategy::WindowedR0,
        folding_steps,
    )
    .expect("Task 8 fixture must admit the continuation plan");
    assert!(
        plan > 0,
        "{TASK8_DIAGNOSTIC}: fixture selected zero continuation passes"
    );

    let point_host: Vec<_> = (0..=folding_steps)
        .map(|coordinate| deterministic_e4(0x300 + coordinate as u32))
        .collect();
    let layers = programs.runtime_circuit().layers.len();
    let accumulator = Arc::new(Mutex::new(Task8DifferentialAccumulator {
        layers,
        coordinates: layers,
        folding_steps: BTreeSet::from([folding_steps]),
        start_rounds: BTreeSet::new(),
        masks: BTreeSet::new(),
        max_sources: 0,
        max_legacy_displacement: 0,
        semantic_comparisons: 0,
        publication_elements_compared: 0,
        comparator_field_coverage_checks: 0,
        mutation_checks: 0,
        source_table_identity_rows: 0,
        source_identity_records: 0,
        source_id_census: std::collections::BTreeMap::new(),
        source_backing_census: std::collections::BTreeMap::new(),
        allocation_records: 0,
        topology_owner_records: 0,
        topology_owner_kinds: BTreeSet::new(),
        topology_coordinates: 0,
        later_start_shared_prior_coordinates: 0,
        multi_source_coordinates: 0,
        arm_memory_comparisons: 0,
        procedural_source_records: 0,
        mutation_families: BTreeSet::new(),
        capacity_overlap_rows: 0,
        capacity_heavy_layers: Vec::new(),
        capacity_publication_bytes: Vec::new(),
        capacity_overlap_live_bytes: Vec::new(),
        capacity_overlap_owner_counts: Vec::new(),
        capacity_physical_peak_bytes: Vec::new(),
        capacity_logical_peak_bytes: Vec::new(),
        ledger_coordinates: 0,
        ledger_owner_generations: 0,
        ledger_shared_symbol_transitions: 0,
        ledger_enqueue_pointer_records: 0,
        ledger_owner_records: 0,
    }));
    let mut readback_scratch = alloc_static_pinned_box_uninit(TASK8_READBACK_CHUNK_BYTES)?;
    let storage_owner = storage as *const _ as usize;
    for layer in 0..layers {
        let window_program = programs.main_continuation_window_layer(layer);
        let continuation_program = programs.continuation_layer(layer);
        assert_eq!(window_program.layer, continuation_program.layer);
        assert_eq!(
            window_program.coefficients,
            continuation_program.coefficients
        );
        assert_eq!(
            window_program.sources.len(),
            continuation_program.coefficients.sources.len()
        );
        assert!(window_program
            .sources
            .iter()
            .enumerate()
            .all(|(index, source)| {
                source.id.0 as usize == index
                    && source.origin == continuation_program.coefficients.sources[index]
            }));
        let raw_source_count = window_program
            .sources
            .iter()
            .filter(|source| family_read_place(source.raw_family, source.raw_column).is_some())
            .count();
        assert!(raw_source_count > 0, "Task 8 layer retained no raw sources");
        let expected_source_count = window_program.sources.len();
        let procedural_source_count = window_program.sources.len() - raw_source_count;
        let window_sources = schedule_source_identity(
            storage,
            window_program,
            &mut readback_scratch,
            callbacks,
            context,
        )?;
        let legacy_sources = schedule_source_identity(
            storage,
            window_program,
            &mut readback_scratch,
            callbacks,
            context,
        )?;
        let source_table: Arc<Mutex<Option<Vec<Task8SourceIdentityRecord>>>> =
            Arc::new(Mutex::new(None));
        let callback_source_table = Arc::clone(&source_table);
        let callback_source_accumulator = Arc::clone(&accumulator);
        let source_payload = Mutex::new(Some((window_sources, legacy_sources)));
        callbacks.schedule(
            move || {
                let (window_sources, legacy_sources) = source_payload
                    .lock()
                    .expect("Task 8 scheduled source payload mutex poisoned")
                    .take()
                    .expect("Task 8 scheduled source payload consumed twice");
                let window_sources: Vec<_> = window_sources
                    .into_iter()
                    .map(ScheduledSourceIdentityRecord::materialize)
                    .collect();
                let legacy_sources: Vec<_> = legacy_sources
                    .into_iter()
                    .map(ScheduledSourceIdentityRecord::materialize)
                    .collect();
                assert_source_records_nonvacuous(&window_sources, raw_source_count);
                assert_eq!(window_sources, legacy_sources);
                if window_sources.len() > 1 {
                    assert!(
                        window_sources
                            .iter()
                            .map(|record| record.backing_base)
                            .collect::<BTreeSet<_>>()
                            .len()
                            < window_sources.len(),
                        "Task 8 consolidated storage regressed to one allocation per raw source"
                    );
                }
                {
                    let mut state = callback_source_accumulator
                        .lock()
                        .expect("Task 8 source-census accumulator mutex poisoned");
                    assert!(state
                        .source_id_census
                        .insert(
                            layer,
                            window_sources
                                .iter()
                                .map(|record| record.source.0)
                                .collect(),
                        )
                        .is_none());
                    assert!(state
                        .source_backing_census
                        .insert(
                            layer,
                            window_sources
                                .iter()
                                .map(|record| record.backing_base)
                                .collect::<BTreeSet<_>>()
                                .len(),
                        )
                        .is_none());
                }
                let previous = callback_source_table
                    .lock()
                    .expect("Task 8 source-table mutex poisoned")
                    .replace(window_sources);
                assert!(previous.is_none(), "Task 8 source table materialized twice");
            },
            context.get_exec_stream(),
        )?;

        let capacity = run_first_pass_legacy_capacity_probe(
            storage,
            continuation_program,
            inits_and_teardowns_top_bits,
            folding_steps,
            &point_host,
            callbacks,
            context,
        )?;
        assert_eq!(capacity.overlap_event.owners.len(), 2);
        {
            let mut state = accumulator
                .lock()
                .expect("Task 8 differential accumulator mutex poisoned");
            state.capacity_overlap_rows += 1;
            state.source_table_identity_rows += 1;
            state.masks.insert(window_program.shape.bits());
            state.max_sources = state.max_sources.max(window_program.sources.len());
            state.procedural_source_records += procedural_source_count;
            if capacity.publication_bytes > 2usize << 30 {
                state.capacity_heavy_layers.push(layer);
                state
                    .capacity_publication_bytes
                    .push(capacity.publication_bytes);
                state.capacity_overlap_live_bytes.push(
                    capacity
                        .overlap_event
                        .owners
                        .iter()
                        .map(|owner| owner.2)
                        .sum(),
                );
                state
                    .capacity_overlap_owner_counts
                    .push(capacity.overlap_event.owners.len());
                state
                    .capacity_physical_peak_bytes
                    .push(capacity.memory.physical_backing_peak_bytes);
                state
                    .capacity_logical_peak_bytes
                    .push(capacity.memory.logical_live_peak_bytes);
            }
        }
        for pass_index in 0..usize::from(plan) {
            let start_round = 3 * (pass_index + 1);
            let mut owner_ledger = Task8OwnerGenerationLedger::default();
            let (window, carried) = run_window_arm(
                storage,
                window_program,
                continuation_program,
                inits_and_teardowns_top_bits,
                folding_steps,
                start_round,
                &point_host,
                &mut readback_scratch,
                callbacks,
                context,
                &mut owner_ledger,
            )?;
            let (legacy, source_columns, shape, adoption) = run_legacy_arm(
                storage,
                window_program,
                continuation_program,
                inits_and_teardowns_top_bits,
                folding_steps,
                start_round,
                &point_host,
                &mut readback_scratch,
                callbacks,
                context,
                &mut owner_ledger,
                &carried,
            )?;
            let callback_accumulator = Arc::clone(&accumulator);
            let callback_source_table = Arc::clone(&source_table);
            let coordinate_payload = Mutex::new(Some((
                window,
                legacy,
                source_columns,
                shape,
                adoption,
                owner_ledger,
            )));
            callbacks.schedule(
                move || {
                    let (window, legacy, source_columns, shape, adoption, owner_ledger) =
                        coordinate_payload
                            .lock()
                            .expect("Task 8 coordinate payload mutex poisoned")
                            .take()
                            .expect("Task 8 coordinate payload consumed twice");
                    let ledger_shared_symbol_transitions = validate_owner_generation_ledger(
                        &owner_ledger,
                        TASK8_WINDOW_ARM,
                        TASK8_LEGACY_ARM,
                        &TASK8_SHARED_DEVICE_SYMBOLS,
                    );
                    for arm in [TASK8_WINDOW_ARM, TASK8_LEGACY_ARM] {
                        assert_eq!(
                            owner_ledger.arm_labels(arm),
                            expected_arm_owner_labels(arm, start_round, raw_source_count),
                            "Task 8 {arm} arm opened an unexpected owner set"
                        );
                    }
                    assert_eq!(
                        owner_ledger.label_generations(TASK8_WINDOW_ARM, "prior_publication"),
                        start_round / 3 - 1,
                        "Task 8 window arm published an unexpected number of prior levels"
                    );
                    assert_eq!(
                        owner_ledger.label_generations(TASK8_LEGACY_ARM, "prior_publication"),
                        start_round / 3 - 1,
                        "Task 8 legacy arm published an unexpected number of prior levels"
                    );
                    assert_eq!(
                        owner_ledger.label_generations(TASK8_LEGACY_ARM, "publication"),
                        3,
                        "Task 8 legacy arm did not open one publication per round"
                    );
                    assert_eq!(
                        owner_ledger.label_generations(TASK8_WINDOW_ARM, "coefficient_bank"),
                        1
                    );
                    assert_eq!(
                        owner_ledger.label_generations(TASK8_LEGACY_ARM, "coefficient_bank"),
                        1 + usize::from(start_round > 3),
                        "Task 8 legacy arm did not retire the bank its prior passes read"
                    );
                    assert!(
                        owner_ledger.resident_reads(TASK8_WINDOW_ARM) > 0
                            && owner_ledger.resident_reads(TASK8_LEGACY_ARM) > 0,
                        "Task 8 arms read back Eq bytes they never wrote without recording them"
                    );
                    let window_sites = owner_ledger.enqueue_sites(TASK8_WINDOW_ARM);
                    let legacy_sites = owner_ledger.enqueue_sites(TASK8_LEGACY_ARM);
                    let passes = start_round / 3;
                    assert_eq!(window_sites["window-launch"], passes);
                    assert_eq!(window_sites["fold-weight-build"], passes);
                    assert_eq!(window_sites["window-tail-reduce"], 1);
                    assert_eq!(window_sites["window-tail-rounds"], 1);
                    assert_eq!(window_sites["eq-build"], passes);
                    assert_eq!(legacy_sites["segmented-round"], 3);
                    assert_eq!(legacy_sites["dual-finalize"], 3);
                    assert_eq!(legacy_sites["fold-weight-build"], passes - 1 + 3);
                    assert_eq!(legacy_sites["eq-build"], passes);
                    assert_eq!(
                        legacy_sites.get("window-launch"),
                        (passes > 1).then_some(&(passes - 1))
                    );
                    assert!(!legacy_sites.contains_key("window-tail-reduce"));
                    for sites in [&window_sites, &legacy_sites] {
                        assert_eq!(sites["coefficient-bank-fill"], 1);
                        assert_eq!(sites["challenge-slab-slot-copy"], 3);
                        assert_eq!(sites["claim-point-symbol-write"], 1);
                    }
                    let (adoption_mutation_checks, adoption_families) =
                        validate_adoption_mutations(&adoption);
                    let sources = callback_source_table
                        .lock()
                        .expect("Task 8 source-table mutex poisoned")
                        .as_ref()
                        .expect("Task 8 source-table callback did not run")
                        .clone();
                    let (window, window_memory, window_allocations, window_live_mutations) =
                        window.materialize();
                    let (mut legacy, legacy_memory, legacy_allocations, legacy_live_mutations) =
                        legacy.materialize();
                    assert!(legacy_live_mutations.materialize().is_empty());
                    let raw_publication = std::mem::take(&mut legacy.publication);
                    assert_eq!(source_columns.len(), expected_source_count);
                    assert!(source_columns
                        .iter()
                        .enumerate()
                        .all(|(index, (source, _))| source.0 as usize == index));
                    legacy.publication = canonicalize_legacy_publication(
                        &raw_publication,
                        &source_columns,
                        shape.columns,
                        shape.column_elems,
                    )
                    .unwrap_or_else(|error| panic!("Task 8 legacy canonicalization: {error:?}"));
                    assert_eq!(window_memory.start, legacy_memory.start);
                    assert_eq!(window_memory.return_to_entry, window_memory.start);
                    assert_eq!(legacy_memory.return_to_entry, legacy_memory.start);
                    assert!(
                        window_memory.physical_backing_peak_bytes
                            <= legacy_memory.physical_backing_peak_bytes,
                        "Task 8 window arm increased physical backing peak"
                    );
                    assert!(
                        window_memory.logical_live_peak_bytes
                            <= legacy_memory.logical_live_peak_bytes,
                        "Task 8 window arm increased corrected logical peak"
                    );
                    let semantic_comparisons = compare_observations(&window, &legacy)
                        .unwrap_or_else(|error| {
                            panic!("Task 8 prepared-state differential mismatch: {error:?}")
                        });
                    let comparator_field_coverage_checks =
                        run_comparator_field_coverage_checks(&window, &legacy);
                    let mut mutation_checks = 0usize;
                    let (live_mutation_checks, mut mutation_families) =
                        validate_live_observation_mutations(
                            &window,
                            &legacy,
                            window_live_mutations,
                        );
                    mutation_checks += live_mutation_checks;
                    mutation_checks += adoption_mutation_checks;
                    mutation_families.extend(adoption_families);
                    let displaced = source_columns
                        .iter()
                        .filter(|(source, column)| source.0 as usize != *column)
                        .count();
                    if source_columns.len() > 1 {
                        let mut duplicate = source_columns.clone();
                        duplicate[0].0 = duplicate[1].0;
                        assert!(matches!(
                            canonicalize_legacy_publication(
                                &raw_publication,
                                &duplicate,
                                shape.columns,
                                shape.column_elems,
                            ),
                            Err(LegacyPublicationCanonicalizationError::DuplicateSource { .. })
                        ));
                        mutation_checks += 1;
                        mutation_families.insert("duplicate-missing-canonical-map".to_owned());

                        let mut displaced_columns = source_columns.clone();
                        let mut displacement_rejected = false;
                        'outer: for left in 0..displaced_columns.len() {
                            for right in left + 1..displaced_columns.len() {
                                displaced_columns.swap(left, right);
                                displaced_columns[left].0 = source_columns[left].0;
                                displaced_columns[right].0 = source_columns[right].0;
                                let displaced_publication = canonicalize_legacy_publication(
                                    &raw_publication,
                                    &displaced_columns,
                                    shape.columns,
                                    shape.column_elems,
                                )
                                .expect("Task 8 valid displaced source map was rejected");
                                if displaced_publication != legacy.publication {
                                    displacement_rejected = true;
                                    break 'outer;
                                }
                                displaced_columns = source_columns.clone();
                            }
                        }
                        assert!(
                            displacement_rejected,
                            "Task 8 source-column displacement mutation was not observable"
                        );
                        mutation_checks += 1;
                        mutation_families.insert("source-column-displacement".to_owned());
                    }
                    let mut missing = source_columns.clone();
                    missing.pop();
                    assert!(matches!(
                        canonicalize_legacy_publication(
                            &raw_publication,
                            &missing,
                            shape.columns,
                            shape.column_elems,
                        ),
                        Err(LegacyPublicationCanonicalizationError::MissingSource { .. })
                    ));
                    mutation_checks += 1;
                    mutation_families.insert("duplicate-missing-canonical-map".to_owned());
                    let window_topology_checks = validate_actual_topology_mutations(
                        storage_owner,
                        &sources,
                        &window_allocations,
                    );
                    let legacy_topology_checks = validate_actual_topology_mutations(
                        storage_owner,
                        &sources,
                        &legacy_allocations,
                    );
                    mutation_checks += window_topology_checks.mutation_checks
                        + legacy_topology_checks.mutation_checks;
                    assert!(
                        window_topology_checks.mutation_checks >= 1
                            && legacy_topology_checks.mutation_checks >= 1
                    );
                    mutation_families.insert("duplicate-raw-owner".to_owned());
                    if start_round > 3 {
                        assert_eq!(window_topology_checks.mutation_checks, 2);
                        assert_eq!(legacy_topology_checks.mutation_checks, 2);
                        mutation_families.insert("overlapping-prior-owner".to_owned());
                    }
                    let mut state = callback_accumulator
                        .lock()
                        .expect("Task 8 differential accumulator mutex poisoned");
                    state.start_rounds.insert(start_round);
                    state.max_legacy_displacement = state.max_legacy_displacement.max(displaced);
                    state.semantic_comparisons += semantic_comparisons;
                    state.publication_elements_compared += window.publication.len();
                    state.comparator_field_coverage_checks += comparator_field_coverage_checks;
                    state.mutation_checks += mutation_checks;
                    state.source_identity_records += 2 * sources.len();
                    state.allocation_records += window_allocations.len() + legacy_allocations.len();
                    state.topology_owner_records +=
                        window_topology_checks.owner_records + legacy_topology_checks.owner_records;
                    state
                        .topology_owner_kinds
                        .extend(window_topology_checks.owner_kinds);
                    state
                        .topology_owner_kinds
                        .extend(legacy_topology_checks.owner_kinds);
                    state.topology_coordinates += 1;
                    state.later_start_shared_prior_coordinates += usize::from(start_round > 3);
                    state.multi_source_coordinates += usize::from(source_columns.len() > 1);
                    state.arm_memory_comparisons += 2;
                    state.ledger_coordinates += 1;
                    state.ledger_owner_generations += owner_ledger.generations.len();
                    state.ledger_shared_symbol_transitions += ledger_shared_symbol_transitions;
                    state.ledger_enqueue_pointer_records += owner_ledger
                        .enqueues
                        .iter()
                        .map(|enqueue| enqueue.records)
                        .sum::<usize>();
                    state.ledger_owner_records += owner_ledger
                        .generations
                        .iter()
                        .flat_map(|entry| entry.records.iter())
                        .count();
                    state.mutation_families.extend(mutation_families);
                    drop(raw_publication);
                },
                context.get_exec_stream(),
            )?;
        }
    }
    let scratch_owner = Arc::new(Mutex::new(Some(readback_scratch)));
    let callback_scratch_owner = Arc::clone(&scratch_owner);
    let request = Mutex::new(Some(request));
    callbacks.schedule(
        move || {
            let scratch = callback_scratch_owner
                .lock()
                .expect("Task 8 shared readback scratch mutex poisoned")
                .take()
                .expect("Task 8 shared readback scratch retired twice");
            assert_eq!(scratch.len(), TASK8_READBACK_CHUNK_BYTES);
            drop(scratch);
            let mut state = accumulator
                .lock()
                .expect("Task 8 differential accumulator mutex poisoned");
            assert!(state.semantic_comparisons > 0);
            assert!(state.mutation_checks > 0);
            assert_eq!(state.coordinates, state.layers);
            assert_eq!(state.source_table_identity_rows, state.layers);
            assert_eq!(state.start_rounds.len(), usize::from(plan));
            assert_eq!(state.topology_coordinates, state.layers * usize::from(plan));
            assert_eq!(state.arm_memory_comparisons, 2 * state.topology_coordinates);
            let later_coordinates = state.topology_coordinates - state.layers;
            assert_eq!(state.ledger_coordinates, state.topology_coordinates);
            assert_eq!(
                state.ledger_shared_symbol_transitions,
                TASK8_SHARED_DEVICE_SYMBOLS.len() * state.topology_coordinates
            );
            assert!(
                state.ledger_owner_generations
                    >= (expected_arm_owner_labels(TASK8_WINDOW_ARM, 3, 1).len()
                        + expected_arm_owner_labels(TASK8_LEGACY_ARM, 3, 1).len())
                        * state.topology_coordinates
            );
            assert_eq!(
                state.ledger_enqueue_pointer_records, state.ledger_owner_records,
                "Task 8 ledger lost a pointer record between the enqueue and owner views"
            );
            assert_eq!(
                state.later_start_shared_prior_coordinates,
                later_coordinates
            );
            assert_eq!(
                state.allocation_records,
                19 * state.topology_coordinates + 2 * later_coordinates
            );
            assert_eq!(
                state.mutation_checks,
                16 * state.layers + 22 * later_coordinates + 2 * state.multi_source_coordinates
            );
            assert_eq!(
                state.comparator_field_coverage_checks,
                17 * state.topology_coordinates
            );
            assert_eq!(
                state.semantic_comparisons,
                state.publication_elements_compared
                    + TASK8_NON_PUBLICATION_COMPARISONS * state.topology_coordinates
            );
            assert_eq!(state.capacity_overlap_rows, state.layers);
            assert_eq!(state.source_id_census.len(), state.layers);
            assert_eq!(state.source_backing_census.len(), state.layers);
            assert!(state.source_id_census.iter().enumerate().all(
                |(layer, (actual_layer, sources))| {
                    layer == *actual_layer
                        && !sources.is_empty()
                        && sources.iter().copied().collect::<BTreeSet<_>>().len() == sources.len()
                }
            ));
            let raw_sources: usize = state.source_id_census.values().map(Vec::len).sum();
            assert_eq!(
                state.source_identity_records,
                2 * usize::from(plan) * raw_sources
            );
            let backing_owners: usize = state
                .source_backing_census
                .values()
                .map(|backings| 1 + backings)
                .sum();
            assert_eq!(
                state.topology_owner_records,
                state.allocation_records + 2 * usize::from(plan) * backing_owners
            );
            assert_eq!(
                state.topology_owner_kinds,
                [
                    "bank",
                    "challenges",
                    "coefficients",
                    "descriptor",
                    "eq",
                    "partials",
                    "prior_publication",
                    "production_storage",
                    "publication",
                    "raw_backing",
                    "transcript_claim",
                    "transcript_prefactor",
                    "transcript_seed",
                ]
                .into_iter()
                .map(str::to_owned)
                .collect()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_heavy_layers.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_physical_peak_bytes.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_overlap_live_bytes.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_overlap_owner_counts.len()
            );
            assert_eq!(
                state.capacity_publication_bytes.len(),
                state.capacity_logical_peak_bytes.len()
            );
            assert_eq!(
                state.mutation_families,
                TASK8_MUTATION_FAMILIES
                    .into_iter()
                    .map(str::to_owned)
                    .collect()
            );
            let report = MainContinuationDifferentialReport {
                layers: state.layers,
                coordinates: state.coordinates,
                folding_steps: std::mem::take(&mut state.folding_steps)
                    .into_iter()
                    .collect(),
                start_rounds: std::mem::take(&mut state.start_rounds)
                    .into_iter()
                    .collect(),
                masks: std::mem::take(&mut state.masks).into_iter().collect(),
                max_sources: state.max_sources,
                max_legacy_displacement: state.max_legacy_displacement,
                semantic_comparisons: state.semantic_comparisons,
                publication_elements_compared: state.publication_elements_compared,
                comparator_field_coverage_checks: state.comparator_field_coverage_checks,
                mutation_checks: state.mutation_checks,
                source_table_identity_rows: state.source_table_identity_rows,
                source_identity_records: state.source_identity_records,
                source_id_census: std::mem::take(&mut state.source_id_census)
                    .into_iter()
                    .collect(),
                source_backing_census: std::mem::take(&mut state.source_backing_census)
                    .into_iter()
                    .collect(),
                allocation_records: state.allocation_records,
                topology_owner_records: state.topology_owner_records,
                topology_owner_kinds: std::mem::take(&mut state.topology_owner_kinds)
                    .into_iter()
                    .collect(),
                topology_coordinates: state.topology_coordinates,
                later_start_shared_prior_coordinates: state.later_start_shared_prior_coordinates,
                multi_source_coordinates: state.multi_source_coordinates,
                arm_memory_comparisons: state.arm_memory_comparisons,
                procedural_source_records: state.procedural_source_records,
                mutation_families: std::mem::take(&mut state.mutation_families)
                    .into_iter()
                    .collect(),
                capacity_overlap_rows: state.capacity_overlap_rows,
                capacity_heavy_layers: std::mem::take(&mut state.capacity_heavy_layers),
                capacity_publication_bytes: std::mem::take(&mut state.capacity_publication_bytes),
                capacity_overlap_live_bytes: std::mem::take(&mut state.capacity_overlap_live_bytes),
                capacity_overlap_owner_counts: std::mem::take(
                    &mut state.capacity_overlap_owner_counts,
                ),
                capacity_physical_peak_bytes: std::mem::take(
                    &mut state.capacity_physical_peak_bytes,
                ),
                capacity_logical_peak_bytes: std::mem::take(&mut state.capacity_logical_peak_bytes),
            };
            drop(state);
            request
                .lock()
                .expect("Task 8 terminal request mutex poisoned")
                .take()
                .expect("Task 8 terminal request consumed twice")
                .publish(Ok(report));
        },
        context.get_exec_stream(),
    )?;
    Ok(())
}
