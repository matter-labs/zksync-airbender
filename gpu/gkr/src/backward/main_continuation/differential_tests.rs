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
    task8_register_symbol, task8_symbol, Task8EnqueueKind, Task8EnqueuePlan, Task8ProbeGuard,
    Task8Span,
};
use crate::backward::vm::production_bind::{
    canonicalize_legacy_publication, family_read_place, foldable_eq_variables,
    prepare_continuation_differential_bank, prepare_continuation_differential_rounds,
    BwdSegBankFillSpans, LegacyPublicationCanonicalizationError, Task8LivePublicationEvent,
};
use crate::backward::vm::seg::launch_bwd_seg_build_fold_weights;
use crate::backward::vm::seg_desc::bwd_seg_fold_weight_run;
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
const TASK8_NON_PUBLICATION_COMPARISONS: usize = 12 + 3 + 8 + 1 + 1 + 1;

/// What one ledger row states about the byte range it names. Every row comes
/// from a span the enqueue reported before it ran.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

/// How a generation's ownership of its bytes ended. The ledger needs the end,
/// not only `Final`: `Final` says no further enqueue may name the generation,
/// while the end says whether the bytes went back to the pool, so a later
/// declaration over the same address is reuse rather than a shadow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8OwnershipEnd {
    /// The arm dropped the device allocation and the pool may hand the bytes to
    /// any later request.
    Freed,
    /// A static device symbol the arm stops naming. The storage outlives the
    /// arm; only this arm's generation of it ends.
    SymbolReleased,
    /// A read-only borrow of storage the arm never owned. Nothing is freed and
    /// nothing is handed back; the borrow itself is what ends.
    BorrowClosed,
}

impl Task8OwnershipEnd {
    /// The ends an origin may declare. A borrow can only be closed, and storage
    /// the arm writes can only be freed or released as a symbol, so a missing
    /// free can never be spelled as a borrow closure.
    fn admits(&self, origin: Task8OwnerOrigin) -> bool {
        match origin {
            Task8OwnerOrigin::Borrowed(_) => matches!(self, Task8OwnershipEnd::BorrowClosed),
            Task8OwnerOrigin::ArmOwned | Task8OwnerOrigin::FactoredEq => matches!(
                self,
                Task8OwnershipEnd::Freed | Task8OwnershipEnd::SymbolReleased
            ),
        }
    }
}

/// One generation's ownership end, and the enqueue boundary it happened at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Task8Release {
    at_enqueue: u64,
    end: Task8OwnershipEnd,
}

/// The generation a rejected span or declaration collided with, carried by the
/// error so a failure names the stale owner and not only the new access.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Task8Culprit {
    arm: &'static str,
    label: &'static str,
    generation: u64,
    covered: (usize, usize),
    final_enqueue: Option<u64>,
    released: Option<Task8Release>,
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
    released: Option<Task8Release>,
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
    /// A span whose narrowest unreleased owner has already bound `Final`. The
    /// culprit is that owner, so the failure names the generation the bytes
    /// still belong to.
    UseAfterFinal(Task8Culprit),
    UseBeforeInitialization,
    ResidentReadOfCoveredBytes,
    ResidentReadOfNonEqOwner,
    WriteToBorrowedOwner,
    UnownedSpan,
    /// A declaration over the exact range of a generation that is still live.
    ReuseWithoutFinal(Task8Culprit),
    /// A declaration over bytes a retired generation still owns because its
    /// ownership never ended.
    ReuseWithoutRelease(Task8Culprit),
    /// Two live declarations that overlap without one containing the other, so
    /// neither is a nested view of the other.
    OverlappingLiveDeclaration(Task8Culprit),
    FinalWithoutEnqueue(Task8Culprit),
    FinalAlreadyBound(Task8Culprit),
    ReleaseWithoutFinal(Task8Culprit),
    ReleaseKindMismatch(Task8Culprit),
    AlreadyReleased(Task8Culprit),
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
    /// What the kernel this enqueue launches is about to do, as production
    /// described it before the call. The census below is derived from this and
    /// never from the records under review.
    plan: Option<Task8EnqueuePlan>,
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

    /// The generation that owns `range`: the most specific declaration
    /// containing it, so a sub-buffer such as the reduced tensor takes the spans
    /// inside it from the allocation it lives in.
    ///
    /// A generation whose ownership has ended -- superseded by an admitted
    /// successor, or released back to the pool, the symbol or the lender -- is
    /// not a candidate at all. It is dropped before specificity is decided, so
    /// bytes the allocator has recycled cannot be shadowed by the declaration
    /// that used to hold them.
    ///
    /// A generation that bound `Final` but never released stays authoritative:
    /// it still owns its bytes, so a span inside it is a use after its last
    /// enqueue even while a broader owner is live. That rejection carries the
    /// stale owner's identity.
    ///
    /// Two live candidates of the same width are a ledger fault, not a choice.
    fn owner_of(&self, range: &std::ops::Range<usize>) -> Result<usize, Task8LedgerError> {
        let mut narrowest: Option<usize> = None;
        let mut live: Option<usize> = None;
        let mut retired: Option<usize> = None;
        let mut ambiguous = false;
        for (slot, entry) in self.generations.iter().enumerate() {
            if !entry.within(range) {
                continue;
            }
            if entry.superseded_by.is_some() || entry.released.is_some() {
                continue;
            }
            let width = entry.covered.end - entry.covered.start;
            let open = entry.final_enqueue.is_none();
            match narrowest {
                Some(best) if best < width => continue,
                Some(best) if best == width => {
                    if open {
                        ambiguous |= live.is_some();
                        live = Some(slot);
                    } else if retired.is_none() {
                        retired = Some(slot);
                    }
                }
                _ => {
                    narrowest = Some(width);
                    ambiguous = false;
                    live = open.then_some(slot);
                    retired = (!open).then_some(slot);
                }
            }
        }
        if ambiguous {
            return Err(Task8LedgerError::AmbiguousLiveGeneration);
        }
        match (live, retired) {
            (Some(slot), _) => Ok(slot),
            (None, Some(slot)) => Err(Task8LedgerError::UseAfterFinal(self.culprit(slot))),
            (None, None) => Err(Task8LedgerError::UnownedSpan),
        }
    }

    /// The identity a rejection carries: which generation the new access or
    /// declaration collided with, and how far through retirement it had got.
    fn culprit(&self, slot: usize) -> Task8Culprit {
        let entry = &self.generations[slot];
        Task8Culprit {
            arm: entry.arm,
            label: entry.label,
            generation: entry.generation,
            covered: (entry.covered.start, entry.covered.end),
            final_enqueue: entry.final_enqueue,
            released: entry.released,
        }
    }

    /// Opens a declaration over `owner..owner + bytes`, classifying it against
    /// every generation whose own successor has not already taken over.
    ///
    /// A retired generation at the same base is this declaration's predecessor:
    /// it is the address being taken back, and [`Self::admit_reuse`] decides
    /// whether it may be. Everything else that intersects is judged by what it
    /// still is. A live generation that contains, or is contained by, the new
    /// range is a nested view -- a sub-buffer inside its allocation, a borrowed
    /// element inside a borrowed vector -- and is left alone; the same range
    /// while it is live is a second owner of bytes it still holds. A generation
    /// that bound `Final` but never released still owns its bytes, so declaring
    /// over them is reuse of storage the arm never gave back. A generation that
    /// did release owns nothing, so it constrains nothing.
    fn open(
        &mut self,
        arm: &'static str,
        label: &'static str,
        origin: Task8OwnerOrigin,
        owner: usize,
        bytes: usize,
    ) -> Result<Task8GenerationToken, Task8LedgerError> {
        let covered = owner..owner + bytes;
        let mut predecessor: Option<Task8GenerationToken> = None;
        for slot in 0..self.generations.len() {
            let entry = &self.generations[slot];
            if entry.superseded_by.is_some() {
                continue;
            }
            let live = entry.final_enqueue.is_none();
            if entry.owner == covered.start && !live {
                predecessor = Some(Task8GenerationToken {
                    slot,
                    owner: entry.owner,
                    generation: entry.generation,
                });
                continue;
            }
            if entry.released.is_some() {
                continue;
            }
            if entry.covered.start >= covered.end || covered.start >= entry.covered.end {
                continue;
            }
            if !live {
                return Err(Task8LedgerError::ReuseWithoutRelease(self.culprit(slot)));
            }
            if entry.covered == covered {
                return Err(Task8LedgerError::ReuseWithoutFinal(self.culprit(slot)));
            }
            let nested = (entry.covered.start <= covered.start && covered.end <= entry.covered.end)
                || (covered.start <= entry.covered.start && entry.covered.end <= covered.end);
            if nested {
                continue;
            }
            return Err(Task8LedgerError::OverlappingLiveDeclaration(
                self.culprit(slot),
            ));
        }
        match predecessor {
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
            released: None,
            initialized,
            final_enqueue: None,
            records: Vec::new(),
        });
        token
    }

    /// The only admission a repeated address range has. The predecessor must
    /// have bound `Final` to its own last enqueue, so no queued use of it can
    /// remain, and its ownership must have ended, so the bytes are the
    /// allocator's to hand out again. The successor starts with no coverage of
    /// its own.
    fn admit_reuse(
        &mut self,
        arm: &'static str,
        label: &'static str,
        origin: Task8OwnerOrigin,
        prior: Task8GenerationToken,
        covered: std::ops::Range<usize>,
    ) -> Result<Task8GenerationToken, Task8LedgerError> {
        let slot = self.resolve(prior)?;
        if self.generations[slot].superseded_by.is_some() {
            return Err(Task8LedgerError::StaleToken);
        }
        {
            let entry = &self.generations[slot];
            match entry.final_enqueue {
                None => return Err(Task8LedgerError::ReuseWithoutFinal(self.culprit(slot))),
                Some(bound) if entry.last_enqueue() != Some(bound) => {
                    return Err(Task8LedgerError::ReuseWithoutFinal(self.culprit(slot)))
                }
                Some(_) => {}
            }
            if entry.released.is_none() {
                return Err(Task8LedgerError::ReuseWithoutRelease(self.culprit(slot)));
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
        let culprit = self.culprit(slot);
        let entry = &mut self.generations[slot];
        if entry.final_enqueue.is_some() {
            return Err(Task8LedgerError::FinalAlreadyBound(culprit));
        }
        let bound = entry
            .last_enqueue()
            .ok_or(Task8LedgerError::FinalWithoutEnqueue(culprit))?;
        entry.final_enqueue = Some(bound);
        Ok(bound)
    }

    /// Ends one generation's ownership, exactly once, at the enqueue boundary
    /// the arm reached. `Final` must already be bound -- ownership cannot end
    /// while a queued enqueue may still name the generation -- and the end must
    /// be one its origin admits.
    fn release(
        &mut self,
        owner: Task8GenerationToken,
        end: Task8OwnershipEnd,
    ) -> Result<u64, Task8LedgerError> {
        let slot = self.resolve(owner)?;
        let at_enqueue = self.enqueues.len() as u64;
        let culprit = self.culprit(slot);
        let entry = &mut self.generations[slot];
        if entry.final_enqueue.is_none() {
            return Err(Task8LedgerError::ReleaseWithoutFinal(culprit));
        }
        if entry.released.is_some() {
            return Err(Task8LedgerError::AlreadyReleased(culprit));
        }
        if !end.admits(entry.origin) {
            return Err(Task8LedgerError::ReleaseKindMismatch(culprit));
        }
        entry.released = Some(Task8Release { at_enqueue, end });
        Ok(at_enqueue)
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

    /// Bytes the arm read back that no recorded device producer had written.
    fn resident_read_bytes(&self, arm: &'static str) -> usize {
        self.generations
            .iter()
            .filter(|entry| entry.arm == arm)
            .flat_map(|entry| entry.records.iter())
            .filter(|record| record.use_kind == Task8QueuedUse::ResidentRead)
            .map(|record| record.range.len())
            .sum()
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
                plan: observed.plan.clone(),
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

/// The one retirement operation: bind `Final` to the generation's own last
/// enqueue and end its ownership, both exactly once. Every real ownership end
/// goes through this, so a site cannot bind `Final` and forget the end.
fn ledger_end_ownership(
    ledger: &mut Task8OwnerGenerationLedger,
    owner: &Task8LedgerOwner,
    end: Task8OwnershipEnd,
) -> u64 {
    let bound = ledger_bind_final(ledger, owner);
    ledger.release(owner.token, end).unwrap_or_else(|error| {
        let (arm, label) = (owner.arm, owner.label);
        panic!("Task 8 {arm} arm could not end {label} ownership as {end:?}: {error:?}")
    });
    bound
}

/// Retires an owner whose device allocation the arm drops here: the bytes go
/// back to the pool and any later declaration over them is reuse.
fn ledger_retire(ledger: &mut Task8OwnerGenerationLedger, owner: &Task8LedgerOwner) -> u64 {
    ledger_end_ownership(ledger, owner, Task8OwnershipEnd::Freed)
}

/// Retires an owner backed by a static device symbol. Nothing returns to the
/// pool; this arm's generation of the symbol ends so the next arm may open its
/// own over the same address.
fn ledger_retire_symbol(ledger: &mut Task8OwnerGenerationLedger, owner: &Task8LedgerOwner) -> u64 {
    ledger_end_ownership(ledger, owner, Task8OwnershipEnd::SymbolReleased)
}

/// Closes a borrow of storage the arm never owned. Distinct from a free on
/// purpose: production keeps the bytes, so this end can never stand in for a
/// missing free.
fn ledger_close_borrow(ledger: &mut Task8OwnerGenerationLedger, owner: &Task8LedgerOwner) -> u64 {
    ledger_end_ownership(ledger, owner, Task8OwnershipEnd::BorrowClosed)
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

/// The census one guarded enqueue must carry, derived from the production plan
/// that enqueue reported before its call and compared against the records the
/// ledger holds for it. Nothing here is computed from those records, so a
/// builder that narrows, widens, misplaces, duplicates or drops one of the
/// guarded ranges disagrees with the plan.
fn validate_enqueue_census(ledger: &Task8OwnerGenerationLedger) {
    let element = std::mem::size_of::<E4>();
    for (ordinal, enqueue) in ledger.enqueues.iter().enumerate() {
        let guarded: &[&str] = match enqueue.site {
            "fold-weight-build" => &["ab_gkr_main_layer_claim_point", "bwd_seg_fold_weights"],
            "coefficient-bank-fill" => &["challenge_slab", "coefficient_bank"],
            "window-launch" | "segmented-round" => &[
                "bwd_seg_fold_weights",
                "published_column",
                "ab_gkr_bwd_seg_coeff_bank",
            ],
            _ => continue,
        };
        let plan = enqueue.plan.as_ref().unwrap_or_else(|| {
            panic!(
                "Task 8 {} enqueue reported no production plan to check its ranges against",
                enqueue.site
            )
        });
        let base_of = |label: &'static str| {
            ledger
                .generations
                .iter()
                .find(|entry| entry.arm == enqueue.arm && entry.label == label)
                .map(|entry| entry.covered.clone())
                .unwrap_or_else(|| panic!("Task 8 {} arm never opened {label}", enqueue.arm))
        };
        let mut expected: Vec<(&'static str, Task8QueuedUse, usize, usize)> = Vec::new();
        match plan {
            Task8EnqueuePlan::FoldWeightBuild {
                round,
                fold_weights,
                fold_weight_bytes,
            } => {
                let first = round.saturating_sub(3);
                expected.push((
                    "ab_gkr_main_layer_claim_point",
                    Task8QueuedUse::Read,
                    base_of("claim_point_symbol").start + first * element,
                    (round - first) * element,
                ));
                expected.push((
                    "bwd_seg_fold_weights",
                    Task8QueuedUse::Write,
                    *fold_weights,
                    *fold_weight_bytes,
                ));
            }
            Task8EnqueuePlan::CoefficientFill {
                slab,
                challenge_slots,
                bank_first,
                bank_bytes,
            } => {
                for slot in challenge_slots {
                    expected.push((
                        "challenge_slab",
                        Task8QueuedUse::Read,
                        slab + slot * element,
                        element,
                    ));
                }
                expected.push((
                    "coefficient_bank",
                    Task8QueuedUse::Write,
                    *bank_first,
                    *bank_bytes,
                ));
            }
            Task8EnqueuePlan::Folding {
                deltas,
                publications,
            } => {
                let weights = base_of("fold_weights_symbol");
                for delta in deltas {
                    let run = bwd_seg_fold_weight_run(*delta);
                    if run.is_empty() {
                        continue;
                    }
                    expected.push((
                        "bwd_seg_fold_weights",
                        Task8QueuedUse::Read,
                        weights.start + run.start * element,
                        (run.end - run.start) * element,
                    ));
                }
                for (address, bytes) in publications {
                    expected.push(("published_column", Task8QueuedUse::Write, *address, *bytes));
                    expected.push(("published_column", Task8QueuedUse::Read, *address, *bytes));
                }
                let bank = base_of("coefficient_bank");
                expected.push((
                    "ab_gkr_bwd_seg_coeff_bank",
                    Task8QueuedUse::Read,
                    bank.start,
                    bank.end - bank.start,
                ));
            }
        }
        let mut observed: Vec<(&'static str, Task8QueuedUse, usize, usize)> = ledger
            .generations
            .iter()
            .flat_map(|entry| entry.records.iter())
            .filter(|record| record.enqueue == ordinal as u64 && guarded.contains(&record.role))
            .map(|record| {
                (
                    record.role,
                    record.use_kind,
                    record.address,
                    record.range.len(),
                )
            })
            .collect();
        observed.sort();
        expected.sort();
        assert_eq!(
            observed, expected,
            "Task 8 {} enqueue does not name the exact ranges its plan describes",
            enqueue.site
        );
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
        let released = entry
            .released
            .unwrap_or_else(|| panic!("Task 8 {} never released ownership", entry.label));
        assert!(
            released.end.admits(entry.origin),
            "Task 8 {} ended {:?} ownership as {:?}",
            entry.label,
            entry.origin,
            released.end
        );
        assert!(
            released.at_enqueue >= bound,
            "Task 8 {} released before Final",
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
    boundary: (u8, u8, u32),
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
    boundary: (u8, u8, u32),
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

/// The number of external challenges the segmented challenge slab consumes:
/// the six permutation linearization challenges plus the additive part.
const TASK8_EXTERNAL_CHALLENGES: usize = 7;

/// Production-shaped device inputs one layer's differential consumes. The only
/// host-to-device copies are the initial inputs — the external challenges and
/// the transcript seed constant, the same class production's input transfer
/// carries. Everything transcript-derived (the lookup challenges, the claim
/// point and its batching slot, and the starting claim and Eq prefactor) is
/// squeezed on the device by the production transcript kernel; both arms
/// consume the same device-resident values, and the host learns them only
/// through the observation readback.
struct Task8DeviceInputs {
    /// `[external(7) | lookup(mul, add) | point + batching (fs + 1) | claim, prefactor]`.
    master: DeviceAllocation<E4>,
    /// The post-draw transcript seed both arms start from.
    seed_master: DeviceAllocation<u32>,
    folding_steps: usize,
    /// Initial-input staging, held as a plain host keepalive until the stream
    /// has drained — never through a callback.
    _external_staging: StaticPinnedBox<E4>,
    _seed_staging: StaticPinnedBox<u32>,
}

impl Task8DeviceInputs {
    fn lookup_offset() -> usize {
        TASK8_EXTERNAL_CHALLENGES
    }
    fn point_offset() -> usize {
        Self::lookup_offset() + 2
    }
    fn state_offset(&self) -> usize {
        Self::point_offset() + self.folding_steps + 1
    }
    fn len(&self) -> usize {
        self.state_offset() + 2
    }
    fn external_ptr(&self) -> *const E4 {
        self.master.as_ptr()
    }
    fn lookup_mul_ptr(&self) -> *const E4 {
        // SAFETY: the master layout above owns these offsets.
        unsafe { self.master.as_ptr().add(Self::lookup_offset()) }
    }
    fn lookup_add_ptr(&self) -> *const E4 {
        // SAFETY: as above.
        unsafe { self.master.as_ptr().add(Self::lookup_offset() + 1) }
    }
    fn point_ptr(&self) -> *const E4 {
        // SAFETY: as above.
        unsafe { self.master.as_ptr().add(Self::point_offset()) }
    }
    fn batching_ptr(&self) -> *const E4 {
        // SAFETY: as above.
        unsafe {
            self.master
                .as_ptr()
                .add(Self::point_offset() + self.folding_steps)
        }
    }
    fn point_len(&self) -> usize {
        self.folding_steps + 1
    }
    fn range(&self, offset: usize, elements: usize) -> (usize, usize) {
        (
            self.master.as_ptr() as usize + offset * std::mem::size_of::<E4>(),
            elements * std::mem::size_of::<E4>(),
        )
    }
}

fn prepare_task8_device_inputs(
    folding_steps: usize,
    context: &ProverContext,
) -> CudaResult<Task8DeviceInputs> {
    let stream = context.get_exec_stream();
    let total = Task8DeviceInputs::point_offset() + folding_steps + 1 + 2;
    let mut master: DeviceAllocation<E4> = context.alloc(total, AllocationPlacement::BestFit)?;
    let external_host: Vec<E4> = (0..TASK8_EXTERNAL_CHALLENGES as u32)
        .map(|i| deterministic_e4(0x100 + i))
        .collect();
    let external_staging = alloc_static_pinned_box_from_slice(&external_host)?;
    memory_copy_async(
        &mut master[..TASK8_EXTERNAL_CHALLENGES],
        &external_staging[..],
        stream,
    )?;
    let seed_host = [0x1020_3040u32, 0x5060_7080, 1, 2, 3, 5, 8, 13];
    let mut seed_master: DeviceAllocation<u32> =
        context.alloc(seed_host.len(), AllocationPlacement::BestFit)?;
    let seed_staging = alloc_static_pinned_box_from_slice(&seed_host)?;
    memory_copy_async(&mut seed_master[..], &seed_staging[..], stream)?;
    let lookup = Task8DeviceInputs::lookup_offset();
    let point = Task8DeviceInputs::point_offset();
    let state = point + folding_steps + 1;
    gpu_hash::blake2s::transcript_squeeze_e4(
        &mut seed_master[..],
        &mut master[lookup..point],
        stream,
    )?;
    gpu_hash::blake2s::transcript_squeeze_e4(
        &mut seed_master[..],
        &mut master[point..state],
        stream,
    )?;
    gpu_hash::blake2s::transcript_squeeze_e4(
        &mut seed_master[..],
        &mut master[state..total],
        stream,
    )?;
    Ok(Task8DeviceInputs {
        master,
        seed_master,
        folding_steps,
        _external_staging: external_staging,
        _seed_staging: seed_staging,
    })
}

/// Copies the device-squeezed claim point (batching slot included) into the
/// main-layer claim-point symbol — device to device, exactly as production's
/// output claim point lives in the symbol — and registers the address this
/// copy hands the runtime, so later launches that read the symbol without
/// naming it can record an exact range against it.
fn copy_claim_point_symbol(
    context: &ProverContext,
    inputs: &Task8DeviceInputs,
) -> CudaResult<usize> {
    let symbol = get_main_layer_claim_point_device_ptr();
    let elements = inputs.point_len();
    // SAFETY: the main-layer claim-point symbol is sized for every admitted
    // folding width; the corpus maximum is pinned independently by preflight.
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(symbol, elements) };
    let bytes = elements * std::mem::size_of::<E4>();
    task8_register_symbol("ab_gkr_main_layer_claim_point", symbol as usize, bytes);
    crate::backward::task8_enqueue_scope!(_task8, "claim-point-symbol-write", Copy, {
        vec![Task8Span::write(
            "claim_point_symbol",
            symbol as usize,
            bytes,
        )]
    });
    let point = Task8DeviceInputs::point_offset();
    memory_copy_async(
        destination,
        &inputs.master[point..point + elements],
        context.get_exec_stream(),
    )?;
    Ok(symbol as usize)
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

/// Reads the three drawn challenges back from the claim-point symbol slots the
/// finalizers wrote them into, exactly where production keeps its output claim
/// point.
fn schedule_challenge_symbol_readback(
    symbol: usize,
    owner: &Task8LedgerOwner,
    start_round: usize,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledReadback<E4>> {
    let element = std::mem::size_of::<E4>();
    let base = symbol + start_round * element;
    assert!(base + 3 * element <= owner.base + owner.bytes);
    // SAFETY: the three challenge slots live inside the registered symbol.
    let slots = unsafe { DeviceSlice::from_raw_parts(base as *const E4, 3) };
    let label = owner.label;
    schedule_read_device_chunked(
        &slots,
        scratch,
        callbacks,
        context,
        "challenge-readback",
        move |offset, bytes| vec![Task8Span::read(label, base + offset, bytes)],
    )
}

/// The legacy arm's post-sequence Eq witness: its per-round finalizes fold the
/// arm's own production-coverage base exactly three times. The remaining
/// variable set is the window arm's post-tail set; only the slot partition may
/// differ, so the cross-arm comparison carries the remaining variable count.
fn task8_legacy_eq_boundary(
    start_round: u8,
    folding_steps: usize,
    actual_eq_sizes: GkrEqSizes,
) -> crate::backward::main_layer::execution_plan::MainEqBoundaryWitness {
    let (base, _) = crate::backward::vm::production_bind::task8_differential_eq_plan(
        start_round,
        folding_steps,
    );
    let expected = crate::backward::vm::production_bind::drained_eq_sizes(base, 3);
    assert_eq!(
        actual_eq_sizes, expected,
        "the legacy arm must fold its production-coverage Eq base exactly three times"
    );
    let consumer_round = usize::from(start_round) + 3;
    crate::backward::main_layer::execution_plan::MainEqBoundaryWitness {
        consumer_round: u8::try_from(consumer_round)
            .expect("legacy consumer round does not fit the runtime field"),
        semantic_suffix_offset: u8::try_from(consumer_round + 1)
            .expect("legacy Eq suffix offset does not fit the runtime field"),
        eq_sizes: actual_eq_sizes,
    }
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
    allocations: Vec<Task8AllocationRecord>,
}

/// The arm's mutable transcript state, initialized device-to-device from the
/// seam's squeezed master values so both arms start from the same
/// device-produced seed, claim and Eq prefactor. No host value and no staging
/// exists on this path.
fn transcript_buffers(
    context: &ProverContext,
    inputs: &Task8DeviceInputs,
) -> CudaResult<TranscriptBuffers> {
    let stream = context.get_exec_stream();
    let mut allocations = Vec::new();
    let before_seed = context.get_device_memory_usage();
    let mut seed: DeviceAllocation<u32> =
        context.alloc(inputs.seed_master.len(), AllocationPlacement::BestFit)?;
    let after_seed = context.get_device_memory_usage();
    {
        let destination = seed.as_ptr() as usize;
        crate::backward::task8_enqueue_scope!(_task8, "transcript-state-copy", Copy, {
            vec![Task8Span::write(
                "transcript_seed",
                destination,
                inputs.seed_master.len() * std::mem::size_of::<u32>(),
            )]
        });
        memory_copy_async(&mut seed[..], &inputs.seed_master[..], stream)?;
    }
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
    let state = inputs.state_offset();
    let before_claim = after_seed;
    let mut claim: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::BestFit)?;
    let after_claim = context.get_device_memory_usage();
    {
        let destination = claim.as_ptr() as usize;
        crate::backward::task8_enqueue_scope!(_task8, "transcript-state-copy", Copy, {
            vec![Task8Span::write(
                "transcript_claim",
                destination,
                std::mem::size_of::<E4>(),
            )]
        });
        memory_copy_async(&mut claim[..], &inputs.master[state..state + 1], stream)?;
    }
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
    let mut prefactor: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::BestFit)?;
    let after_prefactor = context.get_device_memory_usage();
    {
        let destination = prefactor.as_ptr() as usize;
        crate::backward::task8_enqueue_scope!(_task8, "transcript-state-copy", Copy, {
            vec![Task8Span::write(
                "transcript_prefactor",
                destination,
                std::mem::size_of::<E4>(),
            )]
        });
        memory_copy_async(
            &mut prefactor[..],
            &inputs.master[state + 1..state + 2],
            stream,
        )?;
    }
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
    Ok(TranscriptBuffers {
        seed,
        claim,
        prefactor,
        coefficients,
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

/// Opens the four challenge owners as read-only borrows over the seam's
/// device-resident master values: the initial-input external challenges and
/// the device-squeezed lookup and batching challenges. Nothing is uploaded and
/// nothing is staged.
const TASK8_SHARED_DEVICE_INPUTS: &str =
    "device-resident production-shaped inputs the seam squeezed before either arm ran";

fn open_challenge_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    inputs: &Task8DeviceInputs,
) -> Task8ChallengeOwners {
    let borrow = |ledger: &mut Task8OwnerGenerationLedger,
                  label: &'static str,
                  (base, bytes): (usize, usize)| {
        ledger_open(
            ledger,
            arm,
            label,
            Task8OwnerOrigin::Borrowed(TASK8_SHARED_DEVICE_INPUTS),
            base,
            bytes,
        )
    };
    Task8ChallengeOwners {
        external: borrow(
            ledger,
            "external_challenges",
            inputs.range(0, TASK8_EXTERNAL_CHALLENGES),
        ),
        lookup_multiplicative: borrow(
            ledger,
            "lookup_multiplicative",
            inputs.range(Task8DeviceInputs::lookup_offset(), 1),
        ),
        lookup_additive: borrow(
            ledger,
            "lookup_additive",
            inputs.range(Task8DeviceInputs::lookup_offset() + 1, 1),
        ),
        claim_batching: borrow(
            ledger,
            "claim_batching",
            inputs.range(Task8DeviceInputs::point_offset() + inputs.folding_steps, 1),
        ),
    }
}

/// Opens the challenge slab and staged-table owners from the spans the fill
/// itself reported, and the coefficient bank from the symbol it registered.
fn open_bank_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    owners: &mut Task8ArmOwners,
    spans: BwdSegBankFillSpans,
) -> Task8LedgerOwner {
    let arm = owners.arm;
    let slab = ledger_open(
        ledger,
        arm,
        "challenge_slab",
        Task8OwnerOrigin::ArmOwned,
        spans.slab.0,
        spans.slab.1,
    );
    open_reported_symbols(ledger, owners);
    assert_eq!(
        owners
            .coefficient_bank
            .map(|owner| (owner.base, owner.bytes)),
        Some(spans.bank),
        "Task 8 bank fill reported a span the probe did not register"
    );
    slab
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
        "claim_batching",
        "claim_point",
        "claim_point_symbol",
        "coefficient_bank",
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

/// The seam's challenge views are borrows of device-resident production input.
/// Nothing is freed here; the borrow ends.
fn close_challenge_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    challenges: &Task8ChallengeOwners,
) {
    for owner in [
        &challenges.external,
        &challenges.lookup_multiplicative,
        &challenges.lookup_additive,
        &challenges.claim_batching,
    ] {
        ledger_close_borrow(ledger, owner);
    }
}

/// The transcript buffers are this arm's own allocations and are dropped right
/// after this call.
fn retire_transcript_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    transcript: &Task8TranscriptOwners,
) {
    for owner in [
        &transcript.seed,
        &transcript.claim,
        &transcript.prefactor,
        &transcript.coefficients,
    ] {
        ledger_retire(ledger, owner);
    }
}

/// Ends every owner the arm still holds, each by what actually happens to its
/// bytes: the Eq and partials allocations are dropped, the claim point and the
/// source backings were only ever borrowed, and the rest are static device
/// symbols this arm stops naming.
fn retire_arm_owners(ledger: &mut Task8OwnerGenerationLedger, owners: &Task8ArmOwners) {
    ledger_close_borrow(ledger, &owners.claim_point);
    for owner in [&owners.eq_low, &owners.partials] {
        ledger_retire(ledger, owner);
    }
    for owner in [&owners.claim_point_symbol, &owners.eq_high] {
        ledger_retire_symbol(ledger, owner);
    }
    for owner in owners.fold_weights.iter().chain(&owners.coefficient_bank) {
        ledger_retire_symbol(ledger, owner);
    }
    for owner in &owners.sources {
        ledger_close_borrow(ledger, owner);
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
        // The previously published level remains a read input to the next
        // continuation enqueue. Its Final is bound by that consumer's
        // retirement facts, not at replacement time.
        let consumed_owner = prior_owner.replace(published);
        if let Some(consumed_owner) = consumed_owner {
            ledger_retire(ledger, &consumed_owner);
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
    inputs: &Task8DeviceInputs,
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
        let (point_base, point_bytes) =
            inputs.range(Task8DeviceInputs::point_offset(), inputs.point_len());
        let claim_point_owner = ledger_open(
            ledger,
            TASK8_WINDOW_ARM,
            "claim_point",
            Task8OwnerOrigin::Borrowed(TASK8_SHARED_DEVICE_INPUTS),
            point_base,
            point_bytes,
        );
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        let claim_point_symbol = copy_claim_point_symbol(context, inputs)?;
        let claim_point_symbol_owner = ledger_open(
            ledger,
            TASK8_WINDOW_ARM,
            "claim_point_symbol",
            Task8OwnerOrigin::ArmOwned,
            claim_point_symbol,
            inputs.point_len() * std::mem::size_of::<E4>(),
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
        let challenge_owners = open_challenge_owners(ledger, TASK8_WINDOW_ARM, inputs);
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
        // The filled static bank is required by every prior fold-weight
        // enqueue; prepare and schedule it before build_prior_level.
        let bank_observer = context.observe_device_memory_high_water();
        let mut bank =
            prepare_continuation_differential_bank(continuation_program, top_bits, context)?;
        let bank_report = bank_observer.finish();
        // The window arm retires the bank slab right after the fill enqueue
        // (`drop(bank)` below), before the prior build: the record must say so,
        // or the pool's reuse of the freed block by a later recorded owner is
        // an address overlap the topology oracle rightly rejects.
        allocations.push(allocation_group_record(
            "bank",
            bank.challenge_slab().as_ptr() as usize,
            1,
            2,
            1,
            "mixed",
            1,
            &bank_report,
        ));
        let bank_spans = bank.schedule(
            inputs.external_ptr(),
            inputs.lookup_mul_ptr(),
            inputs.lookup_add_ptr(),
            inputs.batching_ptr(),
            context,
        )?;
        assert_eq!(bank_spans.slab.0, bank.challenge_slab().as_ptr() as usize);
        let slab = open_bank_owners(ledger, &mut owners, bank_spans);
        carried.coefficient_bank = Some(bank_spans.bank);
        open_reported_symbols(ledger, &mut owners);
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        // Challenge inputs are consumed exclusively by the bank fill. Retire
        // their borrowed owners at that enqueue boundary; the device-resident
        // seam values themselves outlive both arms.
        close_challenge_owners(ledger, &challenge_owners);
        ledger_retire(ledger, &slab);
        drop(bank);

        let before_prior = context.get_device_memory_usage();
        let prior_observer = context.observe_device_memory_high_water();
        let (prior, prior_owner) = build_prior_level(
            storage,
            window_program,
            folding_steps,
            start_round,
            inputs.point_ptr(),
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
            inputs.point_ptr(),
            start_round + 3,
            folding_steps - start_round - 3,
            owners.eq_high.base as *mut E4,
            eq_low.as_mut_ptr(),
            context,
        )?;
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        launch_bwd_seg_build_fold_weights(start_round as u32, context)?;
        // The fold-weight phase has a distinct probe registration boundary
        // from the earlier coefficient-bank fill registration above.
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
        eprintln!(
            "Task 8 window binding allocator report: requested={} physical_delta={} logical_delta={}",
            binding_report.summed_requested_bytes,
            binding_report.return_to_entry.physical_backing_bytes as isize
                - binding_report.start.physical_backing_bytes as isize,
            binding_report.return_to_entry.logical_live_bytes as isize
                - binding_report.start.logical_live_bytes as isize,
        );
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
        let mut transcript = transcript_buffers(context, inputs)?;
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
            prev_claim_coords: unsafe { inputs.point_ptr().add(start_round) },
            seed: transcript.seed.as_mut_ptr(),
            claim: transcript.claim.as_mut_ptr(),
            eq_prefactor: transcript.prefactor.as_mut_ptr(),
            coeffs_out: transcript.coefficients.as_mut_ptr(),
            challenges_out: unsafe { (claim_point_symbol as *mut E4).add(start_round) },
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
        let challenges = schedule_challenge_symbol_readback(
            claim_point_symbol,
            &owners.claim_point_symbol,
            start_round,
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
                &owners.claim_point_symbol,
                start_round + index,
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
            ledger_retire(ledger, prior_owner);
        }
        drop(prior);
        ledger.absorb(TASK8_WINDOW_ARM, &probe);
        ledger_retire(ledger, &publication_owner);
        ledger_retire(ledger, &reduced_tensor);
        drop(launched);
        retire_transcript_owners(ledger, &transcript_owners);
        drop(transcript.seed);
        drop(transcript.claim);
        drop(transcript.prefactor);
        drop(transcript.coefficients);
        retire_arm_owners(ledger, &owners);
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
                    foldable_eq_variables(&boundary.eq_sizes),
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
    inputs: &Task8DeviceInputs,
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
        let (point_base, point_bytes) =
            inputs.range(Task8DeviceInputs::point_offset(), inputs.point_len());
        let claim_point_owner = ledger_open(
            ledger,
            TASK8_LEGACY_ARM,
            "claim_point",
            Task8OwnerOrigin::Borrowed(TASK8_SHARED_DEVICE_INPUTS),
            point_base,
            point_bytes,
        );
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let claim_point_symbol = copy_claim_point_symbol(context, inputs)?;
        let claim_point_symbol_owner = ledger_open(
            ledger,
            TASK8_LEGACY_ARM,
            "claim_point_symbol",
            Task8OwnerOrigin::ArmOwned,
            claim_point_symbol,
            inputs.point_len() * std::mem::size_of::<E4>(),
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
            inputs.point_ptr(),
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
            inputs.point_ptr(),
            start_round + 1,
            folding_steps - start_round - 1,
            owners.eq_high.base as *mut E4,
            eq_low.as_mut_ptr(),
            context,
        )?;
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let pre_sizes = make_eq_sizes(folding_steps - start_round - 1);
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
        let challenge_owners = open_challenge_owners(ledger, TASK8_LEGACY_ARM, inputs);
        let bank_spans = rounds.schedule_bank_fill(
            inputs.external_ptr(),
            inputs.lookup_mul_ptr(),
            inputs.lookup_add_ptr(),
            inputs.batching_ptr(),
            context,
        )?;
        assert_eq!(bank_spans.slab.0, rounds.challenge_slab().as_ptr() as usize);
        if let Some(borrowed_bank) = owners.coefficient_bank.take() {
            ledger_close_borrow(ledger, &borrowed_bank);
        }
        let slab = open_bank_owners(ledger, &mut owners, bank_spans);
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let mut transcript = transcript_buffers(context, inputs)?;
        allocations.append(&mut transcript.allocations);
        let transcript_owners = open_transcript_owners(ledger, TASK8_LEGACY_ARM, &transcript);
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        let mut publications: std::collections::BTreeMap<u8, Task8LedgerOwner> =
            std::collections::BTreeMap::new();
        if let Some(prior_owner) = prior_owner.as_ref() {
            publications.insert(start_round as u8 - 3, *prior_owner);
        }
        let mut raw_publication = None;
        let challenges_symbol = claim_point_symbol;
        let mut live_eq_sizes = pre_sizes;
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
                ledger_retire(ledger, &retired);
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
            let (active_eq_slot_base, active_eq_size_before_fold) =
                resolve_active_eq_slot(&live_eq_sizes, eq_low.as_mut_ptr());
            launch_backward_dual_finalize_from_partials(
                partials.as_ptr(),
                warp_partial_count(acc_size),
                unsafe { inputs.point_ptr().add(round) },
                transcript.seed.as_mut_ptr(),
                transcript.claim.as_mut_ptr(),
                transcript.prefactor.as_mut_ptr(),
                unsafe { transcript.coefficients.as_mut_ptr().add(4 * local_round) },
                unsafe { (challenges_symbol as *mut E4).add(round) },
                active_eq_slot_base,
                active_eq_size_before_fold,
                context,
            )?;
            record_active_eq_slot_fold(&mut live_eq_sizes);
            ledger.absorb(TASK8_LEGACY_ARM, &probe);
        }
        let post_sizes = live_eq_sizes;
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
        let challenges = schedule_challenge_symbol_readback(
            challenges_symbol,
            &owners.claim_point_symbol,
            start_round,
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
        let boundary = task8_legacy_eq_boundary(start_round as u8, folding_steps, post_sizes);
        let adoption = Task8AdoptionEvidence {
            had_prior: start_round > 3,
            input_live_before,
            first_deltas,
            first_reads_only_published,
            input_retired: !rounds.expected_input_is_live(),
        };
        ledger.absorb(TASK8_LEGACY_ARM, &probe);
        for (_, owner) in publications.iter() {
            ledger_retire(ledger, owner);
        }
        ledger_retire(ledger, &slab);
        drop(rounds);
        close_challenge_owners(ledger, &challenge_owners);
        retire_transcript_owners(ledger, &transcript_owners);
        drop(transcript.seed);
        drop(transcript.claim);
        drop(transcript.prefactor);
        drop(transcript.coefficients);
        retire_arm_owners(ledger, &owners);
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
                    foldable_eq_variables(&boundary.eq_sizes),
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
    inputs: &Task8DeviceInputs,
    _callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<Task8CapacityEvidence> {
    let entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (publication_bytes, overlap_event) = {
        let _ = copy_claim_point_symbol(context, inputs)?;
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;

        launch_build_eq_high_and_low_groups_from_point(
            inputs.point_ptr(),
            4,
            folding_steps - 4,
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
        let _ = rounds.schedule_bank_fill(
            inputs.external_ptr(),
            inputs.lookup_mul_ptr(),
            inputs.lookup_add_ptr(),
            inputs.batching_ptr(),
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
        drop(rounds);
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
    if window.boundary != legacy.boundary {
        return Err(ObservationMismatch::Boundary);
    }
    Ok(window.publication.len()
        + window.coefficients.len()
        + window.challenges.len()
        + window.seed.len()
        + window.claim.len()
        + window.eq_prefactor.len()
        + 1)
}

/// Host model of the Eq bytes one arm reads back without any recorded device
/// producer having written them: the full low buffer and both high slabs are
/// read back before and after the tail, and the union of the arm's real
/// builds — one per prior pass plus the comparison build, each writing both
/// slab sentinels, its used group tables, and its `2^low` prefix — is what the
/// recorded write spans cover. The finalize folds rewrite prefixes of built
/// slots, never extending coverage.
fn task8_expected_eq_resident_bytes(
    folding_steps: usize,
    start_round: usize,
    legacy: bool,
) -> usize {
    let element = std::mem::size_of::<E4>();
    let mut counts: Vec<usize> = (3..start_round)
        .step_by(3)
        .map(|pass_start| folding_steps - pass_start - 3)
        .collect();
    counts.push(if legacy {
        folding_steps - start_round - 1
    } else {
        folding_steps - start_round - 3
    });
    let mut low = 0usize;
    // Every build writes both slab sentinels.
    let mut high = [1usize, 1usize];
    for count in counts {
        let sizes = make_eq_sizes(count);
        low = low.max(1usize << sizes.low);
        for (slot, bits) in sizes.high.iter().enumerate() {
            if *bits > 0 {
                high[slot] = high[slot].max(1usize << bits);
            }
        }
    }
    let uncovered = (GKR_EQ_GROUP_TABLE_LEN - low.min(GKR_EQ_GROUP_TABLE_LEN))
        + (GKR_EQ_GROUP_TABLE_LEN - high[0])
        + (GKR_EQ_GROUP_TABLE_LEN - high[1]);
    // Read back twice: the pre-tail and post-tail observations.
    2 * uncovered * element
}

/// Host model of one arm's factored-Eq state: the ascending coordinates each
/// slot holds. The build kernel assigns group 0 — the top eight coordinates —
/// to `high[0]`, the next eight to `high[1]`, and the last group, the lowest
/// coordinates, to the low buffer, pairing slot bit `j` with the slot's j-th
/// lowest coordinate. A fold removes the lowest coordinate of the lowest
/// non-empty slot, low before high[1] before high[0].
#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8EqCoordinates {
    high: [Vec<usize>; GKR_EQ_HIGH_SLOTS],
    low: Vec<usize>,
}

fn task8_eq_coordinates(offset: usize, count: usize) -> Task8EqCoordinates {
    let mut group_sizes = Vec::new();
    let mut consumed = 0usize;
    while consumed < count {
        let size = (count - consumed).min(8);
        group_sizes.push(size);
        consumed += size;
    }
    let mut high: [Vec<usize>; GKR_EQ_HIGH_SLOTS] = Default::default();
    let mut low = Vec::new();
    let mut top = offset + count;
    for (group, size) in group_sizes.iter().copied().enumerate() {
        let span: Vec<usize> = (top - size..top).collect();
        if group + 1 == group_sizes.len() {
            low = span;
        } else {
            high[group] = span;
        }
        top -= size;
    }
    assert_eq!(top, offset);
    Task8EqCoordinates { high, low }
}

impl Task8EqCoordinates {
    fn fold(&mut self) {
        if !self.low.is_empty() {
            self.low.remove(0);
        } else if !self.high[1].is_empty() {
            self.high[1].remove(0);
        } else {
            assert!(
                !self.high[0].is_empty(),
                "the modeled factored Eq drained past empty"
            );
            self.high[0].remove(0);
        }
    }

    fn sizes(&self) -> GkrEqSizes {
        GkrEqSizes {
            high: [self.high[0].len() as u32, self.high[1].len() as u32],
            low: self.low.len() as u32,
        }
    }

    fn remaining(&self) -> BTreeSet<usize> {
        self.high
            .iter()
            .flatten()
            .chain(&self.low)
            .copied()
            .collect()
    }
}

/// The exact slot table over `coords` (ascending): entry `i` is the product of
/// `point[c_j]` where bit `j` of `i` is set and `1 - point[c_j]` where it is
/// clear. The empty set yields `[ONE]` — both the build's sentinel and the
/// exact sum a fully drained slot leaves in place.
fn task8_expected_eq_table(point: &[E4], coords: &[usize]) -> Vec<E4> {
    let mut table = Vec::with_capacity(1 << coords.len());
    for entry in 0..1usize << coords.len() {
        let mut value = E4::ONE;
        for (bit, coordinate) in coords.iter().enumerate() {
            let mut weight = point[*coordinate];
            if entry & (1 << bit) == 0 {
                let mut one = E4::ONE;
                one.sub_assign(&weight);
                weight = one;
            }
            value.mul_assign(&weight);
        }
        table.push(value);
    }
    table
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8EqOracleMismatch {
    Sizes,
    LowContent,
    HighContent(usize),
}

/// Validates one arm's Eq readback against the host-expected state: the exact
/// sizes and the exact built (or folded) prefix of every slot. Returns the
/// number of compared elements.
fn validate_arm_eq_observation(
    point: &[E4],
    offset: usize,
    count: usize,
    folds: usize,
    observation: &EqObservation,
) -> Result<usize, Task8EqOracleMismatch> {
    let mut coords = task8_eq_coordinates(offset, count);
    for _ in 0..folds {
        coords.fold();
    }
    let mut expected_sizes = make_eq_sizes(count);
    for _ in 0..folds {
        record_active_eq_slot_fold(&mut expected_sizes);
    }
    assert_eq!(
        coords.sizes(),
        expected_sizes,
        "the host Eq coordinate model diverged from the production drain order"
    );
    if observation.sizes != expected_sizes {
        return Err(Task8EqOracleMismatch::Sizes);
    }
    let mut compared = 0usize;
    let expected_low = task8_expected_eq_table(point, &coords.low);
    if observation.low.len() < expected_low.len()
        || observation.low[..expected_low.len()] != expected_low[..]
    {
        return Err(Task8EqOracleMismatch::LowContent);
    }
    compared += expected_low.len();
    for slot in 0..GKR_EQ_HIGH_SLOTS {
        let expected = task8_expected_eq_table(point, &coords.high[slot]);
        let base = slot * GKR_EQ_GROUP_TABLE_LEN;
        if observation.high.len() < base + expected.len()
            || observation.high[base..base + expected.len()] != expected[..]
        {
            return Err(Task8EqOracleMismatch::HighContent(slot));
        }
        compared += expected.len();
    }
    Ok(compared)
}

/// Proves the per-arm Eq oracle notices every field it validates: the baseline
/// accepts and each single-property mutation of sizes, low content and high
/// content is rejected, for both the pre and the post state.
#[allow(clippy::too_many_arguments)]
fn run_eq_oracle_coverage_checks(
    point: &[E4],
    offset: usize,
    count: usize,
    pre: &EqObservation,
    post: &EqObservation,
    pre_folds: usize,
    post_folds: usize,
) -> usize {
    let mut checks = 0usize;
    for (folds, observation) in [(pre_folds, pre), (post_folds, post)] {
        validate_arm_eq_observation(point, offset, count, folds, observation)
            .expect("Task 8 arm Eq observation failed its host oracle");
        let mut sizes = observation.clone();
        sizes.sizes.low ^= 1;
        assert_eq!(
            validate_arm_eq_observation(point, offset, count, folds, &sizes),
            Err(Task8EqOracleMismatch::Sizes)
        );
        let mut low = observation.clone();
        low.low[0] = deterministic_e4(0x906);
        assert_eq!(
            validate_arm_eq_observation(point, offset, count, folds, &low),
            Err(Task8EqOracleMismatch::LowContent)
        );
        let mut high = observation.clone();
        high.high[0] = deterministic_e4(0x916);
        assert_eq!(
            validate_arm_eq_observation(point, offset, count, folds, &high),
            Err(Task8EqOracleMismatch::HighContent(0))
        );
        checks += 3;
    }
    checks
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
            ObservationMismatch::Boundary,
            Box::new(|value| value.boundary.0 ^= 1),
        ),
        (
            ObservationMismatch::Boundary,
            Box::new(|value| value.boundary.2 ^= 1),
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
    window_eq: (&[E4], usize, usize, usize),
    mutations: ScheduledLiveMutationEvidence,
) -> (usize, BTreeSet<String>) {
    let (point, eq_offset, eq_count, post_folds) = window_eq;
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
                let mut stale = window.post_eq.clone();
                stale.low[index] = e4_value.expect("E4 post-Eq mutation");
                assert_eq!(
                    validate_arm_eq_observation(point, eq_offset, eq_count, post_folds, &stale),
                    Err(Task8EqOracleMismatch::LowContent),
                    "Task 8 live {family} mutation did not reach its Eq oracle"
                );
                families.insert(family.to_owned());
                checks += 1;
                continue;
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
    #[test]
    fn probe_phase_registration_order_is_explicit() {
        let source = include_str!("differential_tests.rs");
        let bank = source.find("let bank_spans = bank.schedule").unwrap();
        let bank_reg = source[bank..]
            .find("open_reported_symbols(ledger, &mut owners);")
            .unwrap()
            + bank;
        let bank_absorb = source[bank_reg..]
            .find("ledger.absorb(TASK8_WINDOW_ARM, &probe);")
            .unwrap()
            + bank_reg;
        let fold = source
            .find("launch_bwd_seg_build_fold_weights(start_round as u32, context)?")
            .unwrap();
        let fold_reg = source[fold..]
            .find("open_reported_symbols(ledger, &mut owners);")
            .unwrap()
            + fold;
        let fold_absorb = source[fold_reg..]
            .find("ledger.absorb(TASK8_WINDOW_ARM, &probe);")
            .unwrap()
            + fold_reg;
        assert!(bank < bank_reg && bank_reg < bank_absorb);
        assert!(fold < fold_reg && fold_reg < fold_absorb);
    }
    use gpu_prover_context::{PoolMemoryHighWaterReport, PoolMemoryUsage};

    use super::super::abi::{
        MainContinuationWindowDesc as MainContinuationWindowLaunchBinding,
        MainContinuationWindowSourceRecord,
    };
    use super::super::binding::{task8_window_plan, task8_window_spans};
    use super::E4;
    use super::{
        allocation_group_record, build_corpus_census, close_challenge_owners, deterministic_e4,
        eq_readback_spans, ledger_bind_final, ledger_open, ledger_retire,
        record_active_eq_slot_fold, retire_arm_owners, retire_transcript_owners,
        signed_snapshot_delta, task8_eq_coordinates, task8_register_symbol,
        validate_owner_generation_ledger, validate_owner_generation_structure,
        validate_single_owner_topology, BTreeSet, Field, Task8AbsorbedEnqueue,
        Task8AllocationRecord, Task8ArmOwners, Task8CarriedSymbols, Task8ChallengeOwners,
        Task8Culprit, Task8EnqueueKind, Task8EnqueuePlan, Task8GenerationToken, Task8LedgerError,
        Task8LedgerOwner, Task8LedgerRecord, Task8OwnerGeneration, Task8OwnerGenerationLedger,
        Task8OwnerOrigin, Task8OwnershipEnd, Task8ProbeGuard, Task8QueuedUse, Task8Release,
        Task8Span, Task8TopologyError, Task8TranscriptOwners, GKR_EQ_HIGH_SLOTS,
        MAIN_CONTINUATION_WINDOW_TENSOR_CELLS, TASK8_LEGACY_ARM, TASK8_PRODUCTION_STORAGE,
        TASK8_SHARED_DEVICE_INPUTS, TASK8_SHARED_DEVICE_SYMBOLS, TASK8_WINDOW_ARM,
    };
    use crate::backward::kernels::{task8_dual_finalize_spans, task8_eq_build_spans};
    use crate::backward::main_layer::execution_plan::WINDOW_WIDTH;
    use crate::backward::task8_probe::task8_register_descriptor_sources;
    use crate::backward::task8_probe::{task8_enqueue, task8_enqueue_plan};
    use crate::backward::vm::production_bind::{
        drained_eq_sizes, foldable_eq_variables, task8_challenge_prefix_spans,
        task8_challenge_slot_spans, task8_differential_eq_plan, EqDrainSchedule,
    };
    use crate::backward::vm::seg::{task8_fold_weight_spans, task8_seg_plan, task8_seg_spans};
    use crate::backward::vm::seg_coeff_eval::{
        task8_coeff_fill_spans, SegCoeffEvalBlob, SegCoeffEvalChunks, SegCoeffMonomial,
        SegCoeffRecipe, BWD_SEG_CHALLENGE_ABSENT, BWD_SEG_CHALLENGE_CLAIM_BATCHING,
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

    /// The exact split the consumed v18 run rejected: the resident-read bytes
    /// of an Eq readback must equal the full readback range minus the union of
    /// the arm's real recorded producer writes. Green: a faithful build stream
    /// matches the host model, including a full-coverage low table with zero
    /// low residents. Red: a producer write span shortened to half its real
    /// extent shifts the recorded split away from the model.
    #[test]
    fn cpu_main_continuation_task8_eq_resident_bytes_track_producer_spans() {
        use crate::backward::kernels::GKR_EQ_GROUP_TABLE_LEN;
        let element = std::mem::size_of::<E4>();
        let low_base = 0x91_0000usize;
        let high_base = 0x92_0000usize;
        let point_base = 0x93_0000usize;
        let count = 16usize; // {high[0] = 8, low = 8}: a full low table.
        let sizes = make_eq_sizes(count);
        assert_eq!((sizes.high, sizes.low), ([8, 0], 8));

        let run = |shorten_low: bool| -> usize {
            let mut ledger = Task8OwnerGenerationLedger::default();
            let probe = Task8ProbeGuard::install();
            let arm = TASK8_WINDOW_ARM;
            let _point = borrow(
                &mut ledger,
                arm,
                "claim_point",
                point_base,
                (count + 1) * element,
            );
            let owners_low = ledger_open(
                &mut ledger,
                arm,
                "eq",
                Task8OwnerOrigin::FactoredEq,
                low_base,
                GKR_EQ_GROUP_TABLE_LEN * element,
            );
            let owners_high = ledger_open(
                &mut ledger,
                arm,
                "eq_high_symbol",
                Task8OwnerOrigin::FactoredEq,
                high_base,
                2 * GKR_EQ_GROUP_TABLE_LEN * element,
            );
            let mut spans = task8_eq_build_spans(point_base, 0, count, high_base, low_base);
            if shorten_low {
                for span in &mut spans {
                    if span.address == low_base {
                        span.bytes /= 2;
                    }
                }
            }
            enqueue(
                &mut ledger,
                &probe,
                arm,
                "eq-build",
                Task8EnqueueKind::Kernel,
                spans,
            );
            let low = eq_readback_spans(&ledger, &owners_low);
            readback(&mut ledger, &probe, arm, "pre-eq-readback", low);
            let high = eq_readback_spans(&ledger, &owners_high);
            readback(&mut ledger, &probe, arm, "pre-eq-readback", high);
            assert!(probe.finish().is_empty());
            ledger.resident_read_bytes(arm)
        };

        // One readback pass over one build: the full ranges minus the union of
        // the recorded producer writes — a fully covered low table, a fully
        // covered slab 0, and a sentinel-only slab 1.
        let expected = ((GKR_EQ_GROUP_TABLE_LEN - (1 << sizes.low))
            + (GKR_EQ_GROUP_TABLE_LEN - (1 << sizes.high[0]))
            + (GKR_EQ_GROUP_TABLE_LEN - 1))
            * element;
        assert_eq!(run(false), expected);
        assert_eq!(
            run(true),
            expected + (1 << (sizes.low - 1)) * element,
            "a shortened producer write span must surface as resident bytes"
        );
        assert_ne!(run(true), expected);
    }

    /// The exact shape the consumed v17 run rejected: the window arm's bank
    /// slab is retired right after the fill, the pool's best-fit reuse hands
    /// its base to a later transcript buffer, and only a record that tells the
    /// truth about the early retirement is a valid topology. A record claiming
    /// the slab lived to the arm's end must be rejected as an address overlap.
    #[test]
    fn cpu_main_continuation_task8_topology_accepts_early_retired_bank_reuse() {
        let reused_base = 7;
        let mut reuse = valid_topology();
        reuse.push(record("bank", reused_base, 1, 2));
        reuse.push(record("transcript_seed", reused_base, 4, 8));
        validate_single_owner_topology(&reuse).unwrap();

        let mut stale = valid_topology();
        stale.push(record("bank", reused_base, 1, 8));
        stale.push(record("transcript_seed", reused_base, 4, 8));
        assert_eq!(
            validate_single_owner_topology(&stale),
            Err(Task8TopologyError::OverlappingOwner)
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
    // Matches the test blob's recipe count: the registered symbol extent is
    // exactly the filled bank prefix, as in the real fill.
    const TASK8_TEST_BANK_ELEMS: usize = 2;
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
            challenges_out: (TASK8_TEST_CLAIM_POINT_SYMBOL + 3 * TASK8_TEST_ELEMENT) as *mut E4,
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

    /// One guarded enqueue: the spans its builder reports, and the production
    /// plan the same call site carries so the census has an independent source.
    fn enqueue_planned(
        ledger: &mut Task8OwnerGenerationLedger,
        probe: &Task8ProbeGuard,
        arm: &'static str,
        site: &'static str,
        spans: Vec<Task8Span>,
        plan: Task8EnqueuePlan,
    ) {
        {
            let _scope = task8_enqueue(site, Task8EnqueueKind::Kernel, || {
                task8_enqueue_plan(|| plan);
                spans
            });
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

    fn borrow(
        ledger: &mut Task8OwnerGenerationLedger,
        arm: &'static str,
        label: &'static str,
        base: usize,
        bytes: usize,
    ) -> Task8LedgerOwner {
        ledger_open(
            ledger,
            arm,
            label,
            Task8OwnerOrigin::Borrowed(TASK8_SHARED_DEVICE_INPUTS),
            base,
            bytes,
        )
    }

    /// One arm-owned buffer initialized device-to-device from the seam, as the
    /// real transcript buffers are.
    fn state_copy(
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
            "transcript-state-copy",
            Task8EnqueueKind::Copy,
            vec![Task8Span::write(label, base, bytes)],
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
        let claim_point = borrow(
            ledger,
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
            external: borrow(
                ledger,
                arm,
                "external_challenges",
                TASK8_TEST_CHALLENGE_BASE,
                7 * TASK8_TEST_ELEMENT,
            ),
            lookup_multiplicative: borrow(
                ledger,
                arm,
                "lookup_multiplicative",
                TASK8_TEST_CHALLENGE_BASE + 7 * TASK8_TEST_ELEMENT,
                TASK8_TEST_ELEMENT,
            ),
            lookup_additive: borrow(
                ledger,
                arm,
                "lookup_additive",
                TASK8_TEST_CHALLENGE_BASE + 8 * TASK8_TEST_ELEMENT,
                TASK8_TEST_ELEMENT,
            ),
            // Nested inside the borrowed claim point, as the real batching slot
            // is its last element; the narrowest declaration wins the reads.
            claim_batching: borrow(
                ledger,
                arm,
                "claim_batching",
                TASK8_TEST_CLAIM_POINT + (TASK8_TEST_POINT_LEN - 1) * TASK8_TEST_ELEMENT,
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
        let chunks = SegCoeffEvalChunks::build(&task8_test_blob());
        for ((first, count), slots) in chunks
            .task8_chunk_ranges()
            .into_iter()
            .zip(chunks.task8_challenge_slots())
        {
            let bank_first = bank.base + first as usize * TASK8_TEST_ELEMENT;
            let bank_bytes = count as usize * TASK8_TEST_ELEMENT;
            enqueue_planned(
                ledger,
                probe,
                arm,
                "coefficient-bank-fill",
                task8_coeff_fill_spans(slots, slab.base, bank_first, bank_bytes),
                Task8EnqueuePlan::CoefficientFill {
                    slab: slab.base,
                    challenge_slots: slots.to_vec(),
                    bank_first,
                    bank_bytes,
                },
            );
        }
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
            seed: state_copy(
                ledger,
                probe,
                arm,
                "transcript_seed",
                TASK8_TEST_TRANSCRIPT_BASE,
                8 * std::mem::size_of::<u32>(),
            ),
            claim: state_copy(
                ledger,
                probe,
                arm,
                "transcript_claim",
                TASK8_TEST_TRANSCRIPT_BASE + 0x1000,
                TASK8_TEST_ELEMENT,
            ),
            prefactor: state_copy(
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
        };
        Task8ArmFixture {
            owners,
            challenges,
            transcript,
            slab,
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
        enqueue_planned(
            ledger,
            probe,
            owners.arm,
            "fold-weight-build",
            task8_fold_weight_spans(round as u32, TASK8_TEST_FOLD_WEIGHTS),
            Task8EnqueuePlan::FoldWeightBuild {
                round,
                fold_weights: TASK8_TEST_FOLD_WEIGHTS,
                fold_weight_bytes: TASK8_TEST_FOLD_WEIGHT_ELEMS * TASK8_TEST_ELEMENT,
            },
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
        challenge_slots_start: usize,
    ) {
        readback(
            ledger,
            probe,
            arm,
            "challenge-readback",
            vec![Task8Span::read(
                "claim_point_symbol",
                TASK8_TEST_CLAIM_POINT_SYMBOL + challenge_slots_start * TASK8_TEST_ELEMENT,
                3 * TASK8_TEST_ELEMENT,
            )],
        );
        for (owner, site) in [
            (&transcript.coefficients, "coefficient-readback"),
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
        ledger_retire(ledger, &fixture.publication);
        if let Some(reduced_tensor) = fixture.reduced_tensor.as_ref() {
            ledger_retire(ledger, reduced_tensor);
        }
        ledger_retire(ledger, &fixture.slab);
        close_challenge_owners(ledger, &fixture.challenges);
        retire_transcript_owners(ledger, &fixture.transcript);
        retire_arm_owners(ledger, &fixture.owners);
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
        enqueue_planned(
            ledger,
            &probe,
            arm,
            "window-launch",
            task8_window_spans(&window, TASK8_TEST_ROW_TILES),
            task8_window_plan(&window),
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
        replay_readbacks(ledger, &probe, arm, &fixture.transcript, 3);
        replay_eq_readback(ledger, &probe, &fixture.owners, "post-eq-readback");
        live_mutation(ledger, &probe, &fixture.publication, 0);
        for index in [0usize, 4, 8, 1] {
            live_mutation(ledger, &probe, &fixture.transcript.coefficients, index);
        }
        for index in 0..3 {
            live_mutation(
                ledger,
                &probe,
                &fixture.owners.claim_point_symbol,
                3 + index,
            );
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
            enqueue_planned(
                ledger,
                &probe,
                arm,
                "segmented-round",
                task8_seg_spans(&segmented),
                task8_seg_plan(&segmented),
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
                    TASK8_TEST_CLAIM_POINT_SYMBOL + round * TASK8_TEST_ELEMENT,
                    TASK8_TEST_EQ_LOW,
                    {
                        let mut live = task8_test_sizes();
                        for _ in 0..local_round {
                            record_active_eq_slot_fold(&mut live);
                        }
                        live.low
                    },
                ),
            );
        }
        replay_readbacks(ledger, &probe, arm, &fixture.transcript, TASK8_TEST_ROUND);
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

    /// The retirement lifecycle the differential's two arms run over one
    /// shared ledger, kept as a whole-fixture control: every owner both arms
    /// open is retired exactly once, and the second arm's declarations take
    /// the addresses the first arm released.
    #[test]
    fn cpu_legacy_multi_pass_retirement_lifecycle_mutations() {
        let green = replay_both_orders(TASK8_LEGACY_ARM, TASK8_WINDOW_ARM);
        assert!(validate(&green, TASK8_LEGACY_ARM, TASK8_WINDOW_ARM) > 0);
        for entry in &green.generations {
            let released = entry
                .released
                .unwrap_or_else(|| panic!("{} never released ownership", entry.label));
            assert!(released.end.admits(entry.origin));
            assert_eq!(entry.final_enqueue, entry.last_enqueue());
        }

        // Retirement is exactly once: the ledger refuses a second `Final` and a
        // second end of ownership on the same generation.
        let mut repeated = green.clone();
        let token = {
            let entry = &repeated.generations[0];
            Task8GenerationToken {
                slot: 0,
                owner: entry.owner,
                generation: entry.generation,
            }
        };
        assert!(matches!(repeated.bind_final(token), Err(Task8LedgerError::FinalAlreadyBound(_))));
        assert!(matches!(repeated.release(token, Task8OwnershipEnd::Freed), Err(Task8LedgerError::AlreadyReleased(_))));

        // Premature Final must reproduce the UseAfterFinal/last-use failure.
        let slot = green
            .generations
            .iter()
            .position(|entry| entry.arm == TASK8_LEGACY_ARM && entry.label == "publication")
            .expect("legacy publication generation");
        let mut premature = green.clone();
        premature.generations[slot].final_enqueue = Some(
            premature.generations[slot]
                .records
                .first()
                .expect("publication use")
                .enqueue,
        );
        assert!(validator_rejects(
            &premature,
            TASK8_LEGACY_ARM,
            TASK8_WINDOW_ARM
        ));

        // Omitting Final is rejected by the structural validator.
        let mut omitted = green.clone();
        omitted.generations[slot].final_enqueue = None;
        assert!(validator_rejects(
            &omitted,
            TASK8_LEGACY_ARM,
            TASK8_WINDOW_ARM
        ));

        // A successor at an overlapping address must be generation-aware and
        // must not satisfy the predecessor's retirement predicate.
        assert_eq!(overlap_successor_owner(TASK8_LEGACY_ARM), "reduced_tensor");
    }

    // ------------------------------------------------------------------
    // Release-aware prior-publication lifecycle
    //
    // The GPU failure this replays is a legacy `published_column` write landing
    // on bytes a retired window-arm generation still claimed. Nothing about it
    // needs a device: it is the ledger deciding which generation owns an
    // address after the pool recycled it. The replay drives the ledger through
    // the real control flow of `build_prior_level` plus each arm's own
    // comparison launch, over a pool that recycles exactly as the device pool
    // did, and asserts ownership by identity rather than by "it did not panic".
    // ------------------------------------------------------------------

    /// Every admitted comparison start round.
    const TASK8_REPLAY_START_ROUNDS: [usize; 6] = [3, 6, 9, 12, 15, 18];
    /// A synthetic arena base, well clear of the fixed fixture addresses above.
    const TASK8_REPLAY_ARENA: usize = 0x1000_0000;
    /// One published column, the size the rejected run named.
    const TASK8_REPLAY_COLUMN: usize = 1 << 20;
    const TASK8_REPLAY_COLUMNS: usize = 2;

    /// A deterministic stand-in for the device pool: first fit over a
    /// coalescing free list. An arm that frees adjacent blocks hands the next
    /// arm one wider block, so the second arm's first publication lands on top
    /// of storage the first arm's narrower generations used to own -- the
    /// recycling that put a retired window generation under a legacy column.
    struct Task8ReplayPool {
        cursor: usize,
        free: Vec<(usize, usize)>,
    }

    impl Task8ReplayPool {
        fn new() -> Self {
            Self {
                cursor: TASK8_REPLAY_ARENA,
                free: Vec::new(),
            }
        }

        fn alloc(&mut self, bytes: usize) -> usize {
            if let Some(index) = self.free.iter().position(|&(_, size)| size >= bytes) {
                let (base, size) = self.free.remove(index);
                if size > bytes {
                    self.free.push((base + bytes, size - bytes));
                    self.free.sort();
                }
                return base;
            }
            let base = self.cursor;
            self.cursor += bytes;
            base
        }

        fn free(&mut self, base: usize, bytes: usize) {
            self.free.push((base, bytes));
            self.free.sort();
            let mut merged: Vec<(usize, usize)> = Vec::new();
            for (base, bytes) in self.free.drain(..) {
                match merged.last_mut() {
                    Some((prior_base, prior_bytes)) if *prior_base + *prior_bytes == base => {
                        *prior_bytes += bytes;
                    }
                    _ => merged.push((base, bytes)),
                }
            }
            self.free = merged;
        }
    }

    /// The publication a pass folds into: every three rounds fold three
    /// variables, so each pass publishes an eighth of the rows the last one did.
    fn replay_publication_bytes(pass_index: usize) -> usize {
        ((TASK8_REPLAY_COLUMNS * TASK8_REPLAY_COLUMN) >> (3 * pass_index))
            .max(TASK8_REPLAY_COLUMNS * 16)
    }

    /// What one coordinate's replay does differently from the accepted flow.
    /// Each value changes exactly one fact, so the control it drives has one
    /// cause.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Task8ReplayMutation {
        /// The accepted flow.
        None,
        /// Bind `Final` at the producing launch instead of at the consumer that
        /// still reads the generation, and never release.
        PrematureFinal,
        /// Bind `Final` at the right consumer but never end ownership, on a
        /// generation nothing later reuses.
        OmittedRelease,
        /// Declare the second arm's first publication over half its real
        /// extent, so its later columns have no successor to own them.
        TruncatedSuccessor,
        /// Leave a first-arm allocation `Final`-bound and unreleased, so the
        /// second arm's publication intersects storage that was never handed
        /// back.
        UnreleasedIntersection,
    }

    /// One arm's replayed owners, the enqueues that consumed them, and which
    /// generation owned the recycled column while this arm's first declaration
    /// over it was still live.
    struct Task8ReplayArm {
        scratch: Option<Task8LedgerOwner>,
        priors: Vec<Task8LedgerOwner>,
        publication: Task8LedgerOwner,
        prior_launches: Vec<u64>,
        comparison_launch: u64,
        recycled_column_owner: Option<Result<u64, Task8LedgerError>>,
    }

    /// Opens a declaration the way production does, but fallibly: the controls
    /// assert the typed rejection rather than catching a panic.
    fn replay_open(
        ledger: &mut Task8OwnerGenerationLedger,
        arm: &'static str,
        label: &'static str,
        base: usize,
        bytes: usize,
    ) -> Result<Task8LedgerOwner, Task8LedgerError> {
        let token = ledger.open(arm, label, Task8OwnerOrigin::ArmOwned, base, bytes)?;
        Ok(Task8LedgerOwner {
            token,
            arm,
            label,
            base,
            bytes,
        })
    }

    /// Absorbs one enqueue exactly as [`Task8OwnerGenerationLedger::absorb`]
    /// does -- same ordinals, same per-arm probe order, same record order --
    /// and returns the ledger's own error instead of panicking on it.
    fn replay_enqueue(
        ledger: &mut Task8OwnerGenerationLedger,
        arm: &'static str,
        site: &'static str,
        spans: &[Task8Span],
    ) -> Result<u64, Task8LedgerError> {
        let ordinal = ledger.enqueues.len() as u64;
        let probe_ordinal = ledger
            .enqueues
            .iter()
            .rev()
            .find(|enqueue| enqueue.arm == arm)
            .map_or(0, |enqueue| enqueue.probe_ordinal + 1);
        let enqueue = Task8AbsorbedEnqueue {
            ordinal,
            probe_ordinal,
            arm,
            site,
            kind: Task8EnqueueKind::Kernel,
            plan: None,
            records: 0,
            issued_at_open: probe_ordinal,
            issued_at_close: probe_ordinal + 1,
        };
        ledger.enqueues.push(enqueue.clone());
        for span in spans {
            let use_kind = if span.write {
                Task8QueuedUse::Write
            } else {
                Task8QueuedUse::Read
            };
            ledger.record(&enqueue, span.role, span.address, span.bytes, use_kind)?;
        }
        Ok(ordinal)
    }

    /// One publication's columns, as the window binding reports them.
    fn replay_columns(owner: &Task8LedgerOwner, write: bool) -> Vec<Task8Span> {
        let column = owner.bytes / TASK8_REPLAY_COLUMNS;
        (0..TASK8_REPLAY_COLUMNS)
            .map(|index| {
                let address = owner.base + index * column;
                if write {
                    Task8Span::write("published_column", address, column)
                } else {
                    Task8Span::read("published_column", address, column)
                }
            })
            .collect()
    }

    /// Ends one replayed owner's ownership, unless it is the generation a
    /// mutation deliberately leaves owning its bytes after `Final`.
    fn replay_end_ownership(
        ledger: &mut Task8OwnerGenerationLedger,
        owner: &Task8LedgerOwner,
        unreleased: Option<u64>,
    ) {
        if unreleased == Some(owner.token.generation) {
            ledger_bind_final(ledger, owner);
        } else {
            ledger_retire(ledger, owner);
        }
    }

    /// Replays one arm at one coordinate: the prior passes `build_prior_level`
    /// runs, then the arm's own comparison launch, then the arm's frees.
    ///
    /// The first arm also holds one tail scratch block the second arm does not,
    /// which is what leaves the two arms' layouts different enough for the
    /// second arm's first publication to land over the first arm's storage.
    fn replay_prior_lifecycle_arm(
        ledger: &mut Task8OwnerGenerationLedger,
        pool: &mut Task8ReplayPool,
        arm: &'static str,
        start_round: usize,
        mutation: Task8ReplayMutation,
        first_arm: bool,
    ) -> Result<Task8ReplayArm, Task8LedgerError> {
        let passes = start_round / 3 - 1;
        let premature = mutation == Task8ReplayMutation::PrematureFinal;
        // The one generation `UnreleasedIntersection` leaves owning its bytes:
        // this arm's second allocation, which sits above the tail scratch and
        // so intersects the next arm's first publication from a different base.
        let mut unreleased: Option<u64> = None;
        let mut recycled_column_owner = None;
        let column = TASK8_REPLAY_ARENA..TASK8_REPLAY_ARENA + TASK8_REPLAY_COLUMN;
        let scratch = if first_arm {
            let base = pool.alloc(TASK8_REPLAY_COLUMN);
            let scratch = replay_open(ledger, arm, "tail_scratch", base, TASK8_REPLAY_COLUMN)?;
            replay_enqueue(
                ledger,
                arm,
                "tail-scratch-init",
                &[Task8Span::write("tail_scratch", base, TASK8_REPLAY_COLUMN)],
            )?;
            if premature {
                ledger_bind_final(ledger, &scratch);
            }
            Some(scratch)
        } else {
            None
        };
        let mut prior: Option<Task8LedgerOwner> = None;
        let mut priors = Vec::new();
        let mut prior_launches = Vec::new();
        for pass_index in 0..passes {
            let bytes = replay_publication_bytes(pass_index);
            let base = pool.alloc(bytes);
            // Production opens the new publication after the launch allocated
            // it and before the probe is absorbed.
            let published = replay_open(ledger, arm, "prior_publication", base, bytes)?;
            if pass_index == 0 {
                if first_arm && mutation == Task8ReplayMutation::UnreleasedIntersection {
                    unreleased = Some(published.token.generation);
                }
                if !first_arm {
                    recycled_column_owner = Some(
                        ledger
                            .owner_of(&column)
                            .map(|slot| ledger.generations[slot].generation),
                    );
                }
            }
            let mut spans = replay_columns(&published, true);
            if let Some(prior) = prior.as_ref() {
                spans.extend(replay_columns(prior, false));
            }
            let launch = replay_enqueue(ledger, arm, "prior-window-launch", &spans)?;
            prior_launches.push(launch);
            if premature {
                ledger_bind_final(ledger, &published);
            }
            if let Some(consumed) = prior.replace(published) {
                if !premature {
                    replay_end_ownership(ledger, &consumed, unreleased);
                }
                pool.free(consumed.base, consumed.bytes);
            }
            priors.push(published);
        }
        let bytes = replay_publication_bytes(passes);
        let base = pool.alloc(bytes);
        let declared = if mutation == Task8ReplayMutation::TruncatedSuccessor && !first_arm {
            bytes / TASK8_REPLAY_COLUMNS
        } else {
            bytes
        };
        let publication = replay_open(ledger, arm, "publication", base, declared)?;
        if passes == 0 {
            if first_arm && mutation == Task8ReplayMutation::UnreleasedIntersection {
                unreleased = Some(publication.token.generation);
            }
            if !first_arm {
                recycled_column_owner = Some(
                    ledger
                        .owner_of(&column)
                        .map(|slot| ledger.generations[slot].generation),
                );
            }
        }
        let mut spans: Vec<Task8Span> = (0..TASK8_REPLAY_COLUMNS)
            .map(|index| {
                let column = bytes / TASK8_REPLAY_COLUMNS;
                Task8Span::write("published_column", base + index * column, column)
            })
            .collect();
        if let Some(prior) = prior.as_ref() {
            spans.extend(replay_columns(prior, false));
        }
        if let Some(scratch) = scratch.as_ref() {
            spans.push(Task8Span::read("tail_scratch", scratch.base, scratch.bytes));
        }
        let comparison_launch = replay_enqueue(ledger, arm, "comparison-launch", &spans)?;
        if !premature {
            if let Some(consumed) = prior.take() {
                replay_end_ownership(ledger, &consumed, unreleased);
                pool.free(consumed.base, consumed.bytes);
            }
            if mutation == Task8ReplayMutation::OmittedRelease && !first_arm {
                // Nothing reuses the second arm's own publication, so the only
                // thing that can object to the missing end is the validator.
                ledger_bind_final(ledger, &publication);
            } else {
                replay_end_ownership(ledger, &publication, unreleased);
            }
            pool.free(base, bytes);
            if let Some(scratch) = scratch.as_ref() {
                ledger_retire(ledger, scratch);
                pool.free(scratch.base, scratch.bytes);
            }
        }
        Ok(Task8ReplayArm {
            scratch,
            priors,
            publication,
            prior_launches,
            comparison_launch,
            recycled_column_owner,
        })
    }

    struct Task8ReplayCoordinate {
        ledger: Task8OwnerGenerationLedger,
        window: Task8ReplayArm,
        legacy: Task8ReplayArm,
    }

    /// Both arms of one coordinate over one pool, window arm first, exactly as
    /// the differential runs them against one shared ledger.
    fn replay_prior_lifecycle(
        start_round: usize,
        mutation: Task8ReplayMutation,
    ) -> Result<Task8ReplayCoordinate, Task8LedgerError> {
        let mut ledger = Task8OwnerGenerationLedger::default();
        let mut pool = Task8ReplayPool::new();
        let window = replay_prior_lifecycle_arm(
            &mut ledger,
            &mut pool,
            TASK8_WINDOW_ARM,
            start_round,
            mutation,
            true,
        )?;
        let legacy = replay_prior_lifecycle_arm(
            &mut ledger,
            &mut pool,
            TASK8_LEGACY_ARM,
            start_round,
            mutation,
            false,
        )?;
        Ok(Task8ReplayCoordinate {
            ledger,
            window,
            legacy,
        })
    }

    /// The generation a token names, by identity rather than by slot.
    fn replay_generation<'a>(
        ledger: &'a Task8OwnerGenerationLedger,
        owner: &Task8LedgerOwner,
    ) -> &'a Task8OwnerGeneration {
        ledger
            .generations
            .iter()
            .find(|entry| entry.generation == owner.token.generation)
            .expect("the replay owner names a generation")
    }

    /// The culprit identity a rejection must carry for `owner`, in the state
    /// the mutation left it in.
    fn replay_culprit(
        ledger: &Task8OwnerGenerationLedger,
        owner: &Task8LedgerOwner,
        final_enqueue: Option<u64>,
        released: Option<Task8Release>,
    ) -> Task8Culprit {
        let entry = replay_generation(ledger, owner);
        Task8Culprit {
            arm: owner.arm,
            label: owner.label,
            generation: entry.generation,
            covered: (owner.base, owner.base + owner.bytes),
            final_enqueue,
            released,
        }
    }

    #[test]
    fn cpu_main_continuation_task8_prior_publication_lifecycle_retires_exactly_once() {
        for start_round in TASK8_REPLAY_START_ROUNDS {
            let passes = start_round / 3 - 1;
            let replayed = replay_prior_lifecycle(start_round, Task8ReplayMutation::None)
                .unwrap_or_else(|error| {
                    panic!("start round {start_round} replays cleanly, got {error:?}")
                });
            let ledger = &replayed.ledger;
            validate_owner_generation_structure(ledger, TASK8_WINDOW_ARM, TASK8_LEGACY_ARM, &[]);

            // Exact counts. The window arm holds one tail scratch the legacy
            // arm does not; both open one publication per prior pass plus their
            // own.
            assert_eq!(replayed.window.priors.len(), passes);
            assert_eq!(replayed.legacy.priors.len(), passes);
            assert_eq!(
                ledger.label_generations(TASK8_WINDOW_ARM, "prior_publication"),
                passes
            );
            assert_eq!(
                ledger.label_generations(TASK8_LEGACY_ARM, "prior_publication"),
                passes
            );
            assert_eq!(ledger.generations.len(), 2 * passes + 3);
            assert_eq!(ledger.enqueues.len() as u64, 2 * passes as u64 + 3);

            // Every generation retires exactly once: `Final` on its own last
            // enqueue, then one end of ownership, and every one of these is a
            // pool allocation the arm dropped.
            for entry in &ledger.generations {
                assert_eq!(
                    entry.final_enqueue,
                    entry.last_enqueue(),
                    "{} bound Final away from its last enqueue",
                    entry.label
                );
                let released = entry
                    .released
                    .unwrap_or_else(|| panic!("{} never released ownership", entry.label));
                assert_eq!(released.end, Task8OwnershipEnd::Freed);
                assert!(released.at_enqueue >= entry.final_enqueue.unwrap());
            }

            // Owner identity: each intermediate prior is retired by the pass
            // that still reads it, and the last one by the arm's own comparison
            // launch.
            for arm in [&replayed.window, &replayed.legacy] {
                for (index, prior) in arm.priors.iter().enumerate() {
                    let expected = if index + 1 < passes {
                        arm.prior_launches[index + 1]
                    } else {
                        arm.comparison_launch
                    };
                    let entry = replay_generation(ledger, prior);
                    assert_eq!(
                        entry.final_enqueue,
                        Some(expected),
                        "prior {index} of start round {start_round} retired away from its consumer"
                    );
                    assert_eq!(
                        ledger.enqueues[expected as usize].site,
                        if index + 1 < passes {
                            "prior-window-launch"
                        } else {
                            "comparison-launch"
                        }
                    );
                }
            }

            // Successor ownership. The legacy arm's first publication covers
            // the exact bytes the window arm's tail scratch used to own; the
            // released predecessor must not shadow the live successor.
            let scratch = replayed.window.scratch.as_ref().expect("window scratch");
            assert_eq!(scratch.base, TASK8_REPLAY_ARENA);
            assert_eq!(scratch.bytes, TASK8_REPLAY_COLUMN);
            assert!(replay_generation(ledger, scratch).released.is_some());
            let successor = if passes > 0 {
                &replayed.legacy.priors[0]
            } else {
                &replayed.legacy.publication
            };
            assert_eq!(successor.base, TASK8_REPLAY_ARENA);
            assert!(successor.bytes > TASK8_REPLAY_COLUMN);

            // Every generation a successor takes back had already released, and
            // is taken back at its own base by a later declaration.
            for entry in ledger.generations.iter() {
                let Some(successor_generation) = entry.superseded_by else {
                    continue;
                };
                assert!(
                    entry.released.is_some(),
                    "{} was taken back unreleased",
                    entry.label
                );
                let taker = ledger
                    .generations
                    .iter()
                    .find(|candidate| candidate.generation == successor_generation)
                    .expect("the successor generation exists");
                assert!(taker.generation > entry.generation);
                assert_eq!(taker.owner, entry.owner, "reuse is admitted at one base");
            }
            assert_eq!(
                replay_generation(ledger, scratch).superseded_by,
                Some(successor.token.generation),
                "the tail scratch must be taken back by the legacy successor"
            );

            // While that successor was live, the recycled column resolved to it
            // and not to the released predecessor it covers.
            assert_eq!(
                replayed.legacy.recycled_column_owner,
                Some(Ok(successor.token.generation)),
                "start round {start_round} must hand the recycled column to the live successor"
            );
            // And the ledger's own record of that column names the successor.
            let column = TASK8_REPLAY_ARENA..TASK8_REPLAY_ARENA + TASK8_REPLAY_COLUMN;
            let entry = replay_generation(ledger, successor);
            assert_eq!(entry.arm, TASK8_LEGACY_ARM);
            assert!(
                entry.records.iter().any(
                    |record| record.range == column && record.use_kind == Task8QueuedUse::Write
                ),
                "the successor must hold the write of the recycled column"
            );
            let stale = replay_generation(ledger, scratch);
            assert!(
                stale.records.iter().all(|record| record.enqueue
                    < replayed
                        .legacy
                        .prior_launches
                        .first()
                        .copied()
                        .unwrap_or(replayed.legacy.comparison_launch)),
                "the released predecessor must record nothing from the second arm"
            );
        }
    }

    #[test]
    fn cpu_main_continuation_task8_premature_final_names_the_stale_generation() {
        for start_round in TASK8_REPLAY_START_ROUNDS {
            let passes = start_round / 3 - 1;
            let error = replay_prior_lifecycle(start_round, Task8ReplayMutation::PrematureFinal)
                .err()
                .unwrap_or_else(|| {
                    panic!("start round {start_round} must reject a premature Final")
                });
            // The first generation a later enqueue still reads: the pass-0
            // publication where there are prior passes, and the tail scratch the
            // comparison launch reduces through where there are none.
            let reference = replay_prior_lifecycle(start_round, Task8ReplayMutation::None)
                .expect("the accepted flow replays");
            let (owner, bound) = if passes > 0 {
                (
                    &reference.window.priors[0],
                    reference.window.prior_launches[0],
                )
            } else {
                (
                    reference.window.scratch.as_ref().expect("window scratch"),
                    reference
                        .window
                        .prior_launches
                        .first()
                        .copied()
                        .unwrap_or(0),
                )
            };
            let expected = replay_culprit(&reference.ledger, owner, Some(bound), None);
            assert_eq!(
                error,
                Task8LedgerError::UseAfterFinal(expected),
                "start round {start_round} must name the prematurely retired generation"
            );
        }
    }

    #[test]
    fn cpu_main_continuation_task8_omitted_release_is_rejected_as_a_missing_end() {
        for start_round in TASK8_REPLAY_START_ROUNDS {
            let replayed = replay_prior_lifecycle(start_round, Task8ReplayMutation::OmittedRelease)
                .expect("an omitted end is not a ledger error until validation");
            let entry = replay_generation(&replayed.ledger, &replayed.legacy.publication);
            assert_eq!(entry.final_enqueue, entry.last_enqueue());
            assert!(entry.released.is_none());
            let rejection = replay_structure_rejection(&replayed.ledger).unwrap_or_else(|| {
                panic!("start round {start_round} must reject a generation that never released")
            });
            assert!(
                rejection.contains("Task 8 publication never released ownership"),
                "expected the missing end to be the objection, got {rejection:?}"
            );

            // Isolation: the same replay without the mutation is accepted.
            let accepted = replay_prior_lifecycle(start_round, Task8ReplayMutation::None)
                .expect("the accepted flow replays");
            assert!(replay_structure_rejection(&accepted.ledger).is_none());
        }
    }

    #[test]
    fn cpu_main_continuation_task8_wrong_successor_does_not_inherit_ownership() {
        for start_round in TASK8_REPLAY_START_ROUNDS {
            let error =
                replay_prior_lifecycle(start_round, Task8ReplayMutation::TruncatedSuccessor)
                    .err()
                    .unwrap_or_else(|| {
                        panic!("start round {start_round} must reject an uncovered column")
                    });
            // The bytes the truncated successor left out belong to no live
            // generation: ownership follows the successor's own declaration and
            // is never inherited from the retired generations under it.
            assert_eq!(
                error,
                Task8LedgerError::UnownedSpan,
                "start round {start_round} must not hand the column to a stale owner"
            );
        }
    }

    #[test]
    fn cpu_main_continuation_task8_intersecting_reuse_requires_the_release() {
        for start_round in TASK8_REPLAY_START_ROUNDS {
            let error =
                replay_prior_lifecycle(start_round, Task8ReplayMutation::UnreleasedIntersection)
                    .err()
                    .unwrap_or_else(|| {
                        panic!("start round {start_round} must reject unreleased reuse")
                    });
            let reference = replay_prior_lifecycle(start_round, Task8ReplayMutation::None)
                .expect("the accepted flow replays");
            let passes = start_round / 3 - 1;
            // The first-arm allocation that keeps its bytes is its second one:
            // the pass-0 publication where prior passes exist, the arm's own
            // publication otherwise. Either way it sits above the tail scratch,
            // so the second arm's first publication intersects it from a
            // different base and never reaches `admit_reuse`.
            let owner = if passes > 0 {
                &reference.window.priors[0]
            } else {
                &reference.window.publication
            };
            let bound = replay_generation(&reference.ledger, owner)
                .final_enqueue
                .expect("the accepted flow binds Final");
            assert_ne!(owner.base, TASK8_REPLAY_ARENA);
            let successor = TASK8_REPLAY_ARENA..TASK8_REPLAY_ARENA + 2 * TASK8_REPLAY_COLUMN;
            assert!(
                owner.base > successor.start && owner.base < successor.end,
                "the control must intersect the successor from a different base"
            );
            let expected = replay_culprit(&reference.ledger, owner, Some(bound), None);
            assert_eq!(
                error,
                Task8LedgerError::ReuseWithoutRelease(expected),
                "start round {start_round} must name the generation that never released"
            );
        }
    }

    #[test]
    fn cpu_main_continuation_task8_open_preserves_live_nested_declarations() {
        let mut ledger = Task8OwnerGenerationLedger::default();
        let base = TASK8_REPLAY_ARENA;
        let allocation = replay_open(&mut ledger, TASK8_WINDOW_ARM, "publication", base, 4096)
            .expect("the allocation opens");
        replay_enqueue(
            &mut ledger,
            TASK8_WINDOW_ARM,
            "comparison-launch",
            &[Task8Span::write("published_column", base, 4096)],
        )
        .expect("the allocation is written");

        // A narrower view at the same base as a live allocation is a nested
        // declaration, not reuse of that address.
        let nested = replay_open(&mut ledger, TASK8_WINDOW_ARM, "reduced_tensor", base, 1024)
            .expect("a live allocation admits a nested view at its own base");
        assert_eq!(
            ledger.owner_of(&(base..base + 1024)),
            Ok(nested.token.slot),
            "the narrowest live declaration owns the span"
        );
        assert_eq!(
            ledger.owner_of(&(base + 2048..base + 3072)),
            Ok(allocation.token.slot),
            "bytes outside the view still belong to the allocation"
        );

        // The same range while the allocation is live is reuse of a live
        // generation, and is rejected as such.
        assert_eq!(
            ledger.open(
                TASK8_WINDOW_ARM,
                "publication",
                Task8OwnerOrigin::ArmOwned,
                base,
                4096
            ),
            Err(Task8LedgerError::ReuseWithoutFinal(replay_culprit(
                &ledger,
                &allocation,
                None,
                None
            )))
        );
    }

    /// Runs the structural validator over a replayed ledger and reports the
    /// assertion that rejected it, or `None` if it was accepted.
    fn replay_structure_rejection(ledger: &Task8OwnerGenerationLedger) -> Option<String> {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            validate_owner_generation_structure(ledger, TASK8_WINDOW_ARM, TASK8_LEGACY_ARM, &[]);
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

    /// How the exact census names one range, so a control can assert which
    /// range the validator objected to and not merely that it objected.
    fn census_entry(role: &str, use_kind: Task8QueuedUse, address: usize, bytes: usize) -> String {
        format!("({role:?}, {use_kind:?}, {address}, {bytes})")
    }

    /// Asserts that `ledger` is a well-formed capture — the accepted stream with
    /// one range removed or moved — and that the only thing the validator
    /// objects to is that range disagreeing with its enqueue's production plan.
    fn census_rejected_by(
        ledger: &Task8OwnerGenerationLedger,
        first: &'static str,
        second: &'static str,
        site: &str,
        entry: &str,
    ) {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let structural = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            validate_owner_generation_structure(ledger, first, second, &TASK8_SHARED_DEVICE_SYMBOLS)
        }));
        std::panic::set_hook(previous);
        assert!(
            structural.is_ok(),
            "a ledger differing only in {entry} is otherwise a consistent capture"
        );
        let rejection = validator_rejection(ledger, first, second)
            .unwrap_or_else(|| panic!("the validator accepted a census missing {entry}"));
        let expected =
            format!("Task 8 {site} enqueue does not name the exact ranges its plan describes");
        assert!(
            rejection.contains(&expected) && rejection.contains(entry),
            "expected {site} to reject over {entry}, got {rejection:?}"
        );
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

    /// The ledger a capture whose builder reported `target`'s bytes at a
    /// different address or extent would have produced. Only that one record's
    /// address and range change, so the stream, the census counts, the coverage
    /// and every `Final` stay exactly as the accepted ledger has them.
    fn retune_range(
        base: &Task8OwnerGenerationLedger,
        target: Task8OmittedRange,
        address: usize,
        bytes: usize,
    ) -> Task8OwnerGenerationLedger {
        let mut ledger = base.clone();
        let (slot, index) = locate_range(&ledger, target);
        let record = &mut ledger.generations[slot].records[index];
        assert_ne!(
            record.use_kind,
            Task8QueuedUse::Write,
            "retuning a write would also have to move that generation's coverage"
        );
        record.address = address;
        record.range = address..address + bytes;
        ledger
    }

    /// A capture whose first coefficient-bank-fill enqueue of `arm` reported a
    /// plan naming a different bank range. The records are untouched, so the
    /// census — records against the plan — is the only thing that disagrees.
    fn mutate_fill_plan(
        base: &Task8OwnerGenerationLedger,
        arm: &'static str,
        mutate: impl Fn(&mut usize, &mut usize),
    ) -> Task8OwnerGenerationLedger {
        let mut ledger = base.clone();
        let enqueue = ledger
            .enqueues
            .iter_mut()
            .find(|enqueue| enqueue.arm == arm && enqueue.site == "coefficient-bank-fill")
            .expect("the arm must carry a coefficient-bank-fill enqueue");
        match enqueue.plan.as_mut() {
            Some(Task8EnqueuePlan::CoefficientFill {
                bank_first,
                bank_bytes,
                ..
            }) => mutate(bank_first, bank_bytes),
            other => panic!("the fill enqueue carries an unexpected plan: {other:?}"),
        }
        ledger
    }

    /// The one record `target` names, as a generation slot and a position in
    /// that generation's record list.
    fn locate_range(
        ledger: &Task8OwnerGenerationLedger,
        target: Task8OmittedRange,
    ) -> (usize, usize) {
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
        let mut found = None;
        for (slot, entry) in ledger.generations.iter().enumerate() {
            if entry.arm != target.arm {
                continue;
            }
            for (index, record) in entry.records.iter().enumerate() {
                if record.enqueue == ordinal
                    && record.use_kind == target.use_kind
                    && record.address == target.address
                    && record.range.len() == target.bytes
                {
                    assert!(
                        found.is_none(),
                        "{target:?} does not name exactly one recorded range"
                    );
                    found = Some((slot, index));
                }
            }
        }
        found.unwrap_or_else(|| panic!("{target:?} names no recorded range"))
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
        let (slot, index) = locate_range(&ledger, target);
        let removed = ledger.generations[slot].records.remove(index);
        assert_ne!(
            removed.use_kind,
            Task8QueuedUse::Write,
            "omitting a write would also have to unwind that generation's coverage"
        );
        ledger.enqueues[removed.enqueue as usize].records -= 1;
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

    /// Every coordinate the prepared selector covers, from the fixture census
    /// the selector itself asserts.
    fn task8_selector_coordinates() -> impl Iterator<Item = (usize, usize)> {
        [20usize, 22, 23, 24].into_iter().flat_map(|folding_steps| {
            [3usize, 6, 9, 12, 15, 18]
                .into_iter()
                .filter(move |start| start + 2 < folding_steps)
                .map(move |start| (folding_steps, start))
        })
    }

    /// One planned legacy round's declared Eq state, from the plan the
    /// differential actually hands the segmented planner.
    fn task8_declared_eq(base: GkrEqSizes, schedule: &[u8], round_index: usize) -> GkrEqSizes {
        let plan = EqDrainSchedule::Explicit(schedule);
        drained_eq_sizes(base, plan.drains_through(round_index, schedule.len()))
    }

    /// The production coverage invariant: at every planned round, the
    /// descriptor's factored Eq covers exactly the round's accumulator row
    /// bits. The consumed packet-v8 run failed because the previous plan's
    /// first two scheduled rounds declared the window-shaped base against row
    /// spaces two and one variables wider, so `gkr_compute_eq_inline`
    /// mis-weighted every row.
    #[test]
    fn cpu_main_continuation_differential_eq_plan_matches_every_selector_coordinate() {
        let mut coordinates = 0usize;
        for (folding_steps, start_round) in task8_selector_coordinates() {
            let (base, schedule) = task8_differential_eq_plan(start_round as u8, folding_steps);
            assert_eq!(base, make_eq_sizes(folding_steps - start_round - 1));
            assert_eq!(schedule.len(), folding_steps - start_round);
            assert_eq!(schedule[0], 0);
            assert!(schedule[1..].iter().all(|drains| *drains == 1));

            // Every planned round, not only the three the differential runs:
            // declared Eq bits == accumulator row bits == fs - round - 1.
            for index in 0..schedule.len() {
                let declared = task8_declared_eq(base, &schedule, index);
                let rows_bits = folding_steps - (start_round + index) - 1;
                assert_eq!(
                    foldable_eq_variables(&declared) as usize,
                    rows_bits,
                    "round {index} declares {} Eq variables against {rows_bits} row bits at \
                     folding_steps={folding_steps} start_round={start_round}",
                    foldable_eq_variables(&declared),
                );
            }

            // The three scheduled rounds' declared coordinate coverage is the
            // production absolute set [round + 1, folding_steps).
            for index in 0..WINDOW_WIDTH {
                let mut coords =
                    task8_eq_coordinates(start_round + 1, folding_steps - start_round - 1);
                for _ in 0..index {
                    coords.fold();
                }
                assert_eq!(coords.sizes(), task8_declared_eq(base, &schedule, index));
                assert_eq!(
                    coords.remaining(),
                    (start_round + index + 1..folding_steps).collect::<BTreeSet<_>>(),
                    "round {index} covers the wrong coordinates at \
                     folding_steps={folding_steps} start_round={start_round}"
                );
            }

            // Post-sequence boundary: three folds leave the window arm's exact
            // remaining coordinate set; only the slot partition may differ.
            let mut legacy_post =
                task8_eq_coordinates(start_round + 1, folding_steps - start_round - 1);
            for _ in 0..3 {
                legacy_post.fold();
            }
            let mut window_post = task8_eq_coordinates(
                start_round + WINDOW_WIDTH,
                folding_steps - start_round - WINDOW_WIDTH,
            );
            window_post.fold();
            assert_eq!(legacy_post.remaining(), window_post.remaining());
            assert_eq!(
                legacy_post.remaining(),
                (start_round + 4..folding_steps).collect::<BTreeSet<_>>()
            );
            let mut legacy_sizes = base;
            for _ in 0..3 {
                record_active_eq_slot_fold(&mut legacy_sizes);
            }
            assert_eq!(legacy_post.sizes(), legacy_sizes);
            assert_eq!(
                foldable_eq_variables(&legacy_sizes),
                foldable_eq_variables(&window_post.sizes()),
            );
            coordinates += 1;
        }
        assert_eq!(coordinates, 23, "the selector's coordinate corpus changed");
    }

    /// Every wrong schedule or base the diagnosis predicted must violate the
    /// coverage invariant at some scheduled round of every coordinate — the
    /// consumed v8 plan first among them.
    #[test]
    fn cpu_main_continuation_differential_eq_plan_rejects_wrong_schedules() {
        let mut caught: BTreeSet<&'static str> = BTreeSet::new();
        for (folding_steps, start_round) in task8_selector_coordinates() {
            let (base, schedule) = task8_differential_eq_plan(start_round as u8, folding_steps);
            let rounds = schedule.len();
            let covers = |base: GkrEqSizes, schedule: &[u8]| {
                (0..WINDOW_WIDTH).all(|index| {
                    let plan = EqDrainSchedule::Explicit(schedule);
                    let drains = plan.drains_through(index, schedule.len());
                    u32::from(drains) <= foldable_eq_variables(&base)
                        && foldable_eq_variables(&drained_eq_sizes(base, drains)) as usize
                            == folding_steps - (start_round + index) - 1
                })
            };
            assert!(covers(base, &schedule));

            // The consumed v8 plan: window-shaped base, single deferred fold.
            // Its first two scheduled rounds under-cover their row spaces.
            let stale_base = make_eq_sizes(folding_steps - start_round - WINDOW_WIDTH);
            let mut stale_schedule = vec![0u8; rounds];
            stale_schedule[WINDOW_WIDTH] = 1;
            if !covers(stale_base, &stale_schedule) {
                caught.insert("consumed-v8-plan");
            }
            // Draining from the very first round over-covers nothing and
            // under-covers every round by one.
            let all_drain = vec![1u8; rounds];
            if !covers(base, &all_drain) {
                caught.insert("all-drain-from-start");
            }
            // Never draining leaves rounds one and two over-covered.
            let no_drain = vec![0u8; rounds];
            if !covers(base, &no_drain) {
                caught.insert("no-drain");
            }
            // The drain shifted one round late.
            let mut shifted = vec![1u8; rounds];
            shifted[0] = 0;
            shifted[1] = 0;
            if rounds > 2 {
                shifted[2] = 2;
            }
            if !covers(base, &shifted) {
                caught.insert("shifted-drain");
            }
            // More drains than the base carries: the planner's fail-closed
            // bound, checked here as arithmetic.
            let overrun = vec![1u8; rounds];
            if (0..rounds).any(|index| {
                u32::from(EqDrainSchedule::Explicit(&overrun).drains_through(index, rounds))
                    > foldable_eq_variables(&base)
            }) {
                caught.insert("post-tail-underflow");
            }
        }
        assert_eq!(
            caught.iter().copied().collect::<Vec<_>>(),
            vec![
                "all-drain-from-start",
                "consumed-v8-plan",
                "no-drain",
                "post-tail-underflow",
                "shifted-drain",
            ],
            "a wrong schedule is invisible to the coverage oracle"
        );
    }

    /// The upstream transcript algebra distinguishes the challenge-feedback
    /// defect: a legacy arm that binds later rounds with the original claim
    /// coordinates instead of the drawn challenges agrees on round 0 and
    /// diverges first at `coefficients[4]` — the D1-only prediction of the
    /// bound diagnosis.
    #[test]
    fn cpu_main_continuation_stale_challenge_binding_diverges_at_coefficients_4() {
        use crate::backward::window::reference::tensor_round_tail_reference;

        fn eq_weight(bit: usize, coordinate: E4) -> E4 {
            if bit == 0 {
                let mut weight = E4::ONE;
                weight.sub_assign(&coordinate);
                weight
            } else {
                coordinate
            }
        }

        fn bind_univariate(at_zero: E4, at_one: E4, leading: E4, challenge: E4) -> E4 {
            let mut linear = at_one;
            linear.sub_assign(&leading);
            linear.sub_assign(&at_zero);
            linear.mul_assign(&challenge);
            let mut quadratic = leading;
            quadratic.mul_assign(&challenge);
            quadratic.mul_assign(&challenge);
            let mut bound = at_zero;
            bound.add_assign(&linear);
            bound.add_assign(&quadratic);
            bound
        }

        fn round_update(
            at_zero: E4,
            leading: E4,
            prev_coordinate: E4,
            seed: &mut crate::upstream::Seed,
            claim: &mut E4,
            eq_prefactor: &mut E4,
        ) -> ([E4; 4], E4) {
            use crate::upstream::{
                commit_field_els, draw_random_field_els, evaluate_eq_poly,
                evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
                BabyBearField, Blake2sTranscript,
            };
            let mut normalized_claim = *claim;
            normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));
            let coeffs = output_univariate_monomial_form_max_quadratic::<BabyBearField, E4>(
                prev_coordinate,
                normalized_claim,
                at_zero,
                leading,
            );
            commit_field_els::<BabyBearField, E4, Blake2sTranscript>(seed, &coeffs);
            let challenge =
                draw_random_field_els::<BabyBearField, E4, Blake2sTranscript>(seed, 1)[0];
            *claim = evaluate_small_univariate_poly::<BabyBearField, E4, 4>(&coeffs, &challenge);
            *eq_prefactor = evaluate_eq_poly::<BabyBearField, E4>(&challenge, &prev_coordinate);
            (coeffs, challenge)
        }

        /// The three rounds with each later round's tensor binding taken at
        /// `bind[k]` — the drawn challenge in production, the stale original
        /// coordinate under the D2 defect.
        fn play_rounds(
            tensor: &[E4; 27],
            rho: &[E4; 3],
            seed: [u32; 8],
            claim: E4,
            eq_prefactor: E4,
            stale_bind: [Option<E4>; 2],
        ) -> ([E4; 12], [E4; 3]) {
            let pair_weights: [E4; 4] = core::array::from_fn(|index| {
                let mut weight = eq_weight(index >> 1, rho[1]);
                weight.mul_assign(&eq_weight(index & 1, rho[2]));
                weight
            });
            let single_weights: [E4; 2] = core::array::from_fn(|index| eq_weight(index, rho[2]));
            let contract9 = |cells: &[E4]| {
                let mut accumulator = E4::ZERO;
                for x1 in 0..2 {
                    for x2 in 0..2 {
                        let mut value = cells[3 * x1 + x2];
                        value.mul_assign(&pair_weights[2 * x1 + x2]);
                        accumulator.add_assign(&value);
                    }
                }
                accumulator
            };
            let contract3 = |cells: &[E4]| {
                let mut accumulator = E4::ZERO;
                for x2 in 0..2 {
                    let mut value = cells[x2];
                    value.mul_assign(&single_weights[x2]);
                    accumulator.add_assign(&value);
                }
                accumulator
            };
            let mut seed = crate::upstream::Seed(seed);
            let mut claim = claim;
            let mut eq_prefactor = eq_prefactor;
            let mut coeffs = [E4::ZERO; 12];
            let mut challenges = [E4::ZERO; 3];
            let (round, challenge) = round_update(
                contract9(&tensor[0..9]),
                contract9(&tensor[18..27]),
                rho[0],
                &mut seed,
                &mut claim,
                &mut eq_prefactor,
            );
            coeffs[0..4].copy_from_slice(&round);
            challenges[0] = challenge;
            let bound0 = stale_bind[0].unwrap_or(challenges[0]);
            let bound_nine: [E4; 9] = core::array::from_fn(|index| {
                bind_univariate(tensor[index], tensor[9 + index], tensor[18 + index], bound0)
            });
            let (round, challenge) = round_update(
                contract3(&bound_nine[0..3]),
                contract3(&bound_nine[6..9]),
                rho[1],
                &mut seed,
                &mut claim,
                &mut eq_prefactor,
            );
            coeffs[4..8].copy_from_slice(&round);
            challenges[1] = challenge;
            let bound1 = stale_bind[1].unwrap_or(challenges[1]);
            let bound_three: [E4; 3] = core::array::from_fn(|index| {
                bind_univariate(
                    bound_nine[index],
                    bound_nine[3 + index],
                    bound_nine[6 + index],
                    bound1,
                )
            });
            let (round, challenge) = round_update(
                bound_three[0],
                bound_three[2],
                rho[2],
                &mut seed,
                &mut claim,
                &mut eq_prefactor,
            );
            coeffs[8..12].copy_from_slice(&round);
            challenges[2] = challenge;
            (coeffs, challenges)
        }

        let tensor: [E4; 27] = core::array::from_fn(|index| deterministic_e4(0x700 + index as u32));
        let rho = [
            deterministic_e4(0x7a0),
            deterministic_e4(0x7a1),
            deterministic_e4(0x7a2),
        ];
        let seed = [0x1020_3040u32, 0x5060_7080, 1, 2, 3, 5, 8, 13];
        let claim0 = deterministic_e4(0x51);
        let prefactor0 = deterministic_e4(0x71);

        let mut reference_seed = seed;
        let mut reference_claim = claim0;
        let mut reference_prefactor = prefactor0;
        let (reference_coeffs, reference_challenges) = tensor_round_tail_reference(
            tensor,
            &rho,
            &mut reference_seed,
            &mut reference_claim,
            &mut reference_prefactor,
        );

        // The correct binding reproduces the reviewed window reference exactly.
        let (correct_coeffs, correct_challenges) =
            play_rounds(&tensor, &rho, seed, claim0, prefactor0, [None, None]);
        assert_eq!(correct_coeffs, reference_coeffs);
        assert_eq!(correct_challenges, reference_challenges);

        // D2, with D1 repaired: binding round 1 at the original coordinate
        // instead of the drawn challenge agrees on round 0 and diverges first
        // at coefficients[4].
        let (stale_coeffs, _) = play_rounds(
            &tensor,
            &rho,
            seed,
            claim0,
            prefactor0,
            [Some(rho[0]), None],
        );
        assert_eq!(stale_coeffs[0..4], reference_coeffs[0..4]);
        assert_ne!(
            stale_coeffs[4], reference_coeffs[4],
            "the stale challenge feedback must first surface at coefficients[4]"
        );

        // The same defect one round later: rounds 0-1 agree, round 2 diverges.
        let (late_stale_coeffs, _) = play_rounds(
            &tensor,
            &rho,
            seed,
            claim0,
            prefactor0,
            [None, Some(rho[1])],
        );
        assert_eq!(late_stale_coeffs[0..8], reference_coeffs[0..8]);
        assert_ne!(late_stale_coeffs[8], reference_coeffs[8]);
    }

    /// A schedule that does not cover the sequence exactly fails closed.
    #[test]
    #[should_panic(expected = "one entry per planned round")]
    fn cpu_main_continuation_differential_eq_schedule_length_fails_closed() {
        let (_, schedule) = task8_differential_eq_plan(3, 24);
        let short = &schedule[..schedule.len() - 1];
        EqDrainSchedule::Explicit(short).drains_through(0, schedule.len());
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

            // The coefficient fill's chunks ride the launch parameters by
            // value, so its only reads are the challenge slots the chunk's
            // monomials name, and its writes cover the bank prefix exactly.
            let chunks = SegCoeffEvalChunks::build(&task8_test_blob());
            let expected_slots: Vec<usize> = chunks
                .task8_challenge_slots()
                .iter()
                .flatten()
                .copied()
                .collect();
            assert_eq!(expected_slots, vec![0, 3, 9]);
            let fill = records_of(&ledger, "coefficient-bank-fill");
            assert!(
                fill.iter()
                    .all(|record| record.role != "coefficient_tables"),
                "a by-value fill reads no device table"
            );
            let slots: Vec<_> = fill
                .iter()
                .filter(|record| record.role == "challenge_slab")
                .map(|record| (record.address - TASK8_TEST_SLAB) / element)
                .collect();
            assert_eq!(slots, expected_slots);
            let written: usize = fill
                .iter()
                .filter(|record| record.role == "coefficient_bank")
                .map(|record| record.range.len())
                .sum();
            assert_eq!(
                written,
                chunks.num_coefficients() as usize * element,
                "the chunk writes must cover the bank prefix exactly"
            );
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
            let chunks = SegCoeffEvalChunks::build(&task8_test_blob());

            // Every mutation below changes exactly one range a production
            // builder reported — dropping it, narrowing it, widening it or
            // moving it — and leaves a ledger whose stream, census, coverage and
            // `Final` bindings are the ones that capture would have carried. The
            // census each is checked against comes from the enqueue's own
            // production plan, so each mutant names the range that disagrees.
            let claim = Task8OmittedRange {
                arm: first_arm,
                site: "fold-weight-build",
                occurrence: 0,
                use_kind: Task8QueuedUse::Read,
                address: TASK8_TEST_CLAIM_POINT_SYMBOL + (TASK8_TEST_ROUND - 3) * element,
                bytes: 3 * element,
            };

            // The claim-point coordinates the fold-weight build reads.
            for arm in [first_arm, second_arm] {
                let target = Task8OmittedRange { arm, ..claim };
                census_rejected_by(
                    &omit_range(&base, target),
                    first_arm,
                    second_arm,
                    "fold-weight-build",
                    &census_entry(
                        "ab_gkr_main_layer_claim_point",
                        Task8QueuedUse::Read,
                        target.address,
                        target.bytes,
                    ),
                );
            }
            families.insert("missing-claim-point-range");

            // The same read narrowed to one coordinate: still one record, still
            // inside the initialized claim point, still not the slice the round
            // names.
            census_rejected_by(
                &retune_range(&base, claim, claim.address, element),
                first_arm,
                second_arm,
                "fold-weight-build",
                &census_entry(
                    "ab_gkr_main_layer_claim_point",
                    Task8QueuedUse::Read,
                    claim.address,
                    element,
                ),
            );
            families.insert("narrowed-claim-point-range");

            // The fold-weight run each folding launch reads, in the arm that
            // enqueues that launch.
            let d3 = bwd_seg_fold_weight_run(3);
            let run_target = |arm, site| Task8OmittedRange {
                arm,
                site,
                occurrence: 0,
                use_kind: Task8QueuedUse::Read,
                address: TASK8_TEST_FOLD_WEIGHTS + d3.start * element,
                bytes: (d3.end - d3.start) * element,
            };
            for (arm, site) in [
                (TASK8_WINDOW_ARM, "window-launch"),
                (TASK8_LEGACY_ARM, "segmented-round"),
            ] {
                let target = run_target(arm, site);
                census_rejected_by(
                    &omit_range(&base, target),
                    first_arm,
                    second_arm,
                    site,
                    &census_entry(
                        "bwd_seg_fold_weights",
                        Task8QueuedUse::Read,
                        target.address,
                        target.bytes,
                    ),
                );
            }
            families.insert("missing-fold-weight-run");

            // The window's D3 run widened to the D2+D3 superset, and the
            // segmented round's run moved to the depth-two run no live source
            // folds at. Both stay inside the initialized fold-weight bank.
            let d2 = bwd_seg_fold_weight_run(2);
            for (arm, site, address, bytes) in [
                (
                    TASK8_WINDOW_ARM,
                    "window-launch",
                    TASK8_TEST_FOLD_WEIGHTS + d2.start * element,
                    (d3.end - d2.start) * element,
                ),
                (
                    TASK8_LEGACY_ARM,
                    "segmented-round",
                    TASK8_TEST_FOLD_WEIGHTS + d2.start * element,
                    (d2.end - d2.start) * element,
                ),
            ] {
                census_rejected_by(
                    &retune_range(&base, run_target(arm, site), address, bytes),
                    first_arm,
                    second_arm,
                    site,
                    &census_entry("bwd_seg_fold_weights", Task8QueuedUse::Read, address, bytes),
                );
            }
            families.insert("inexact-fold-weight-run");

            // The chunk's bank write: the plan pins the exact contiguous
            // range, so a builder whose plan narrows it, moves it, or covers a
            // different prefix disagrees with the recorded write.
            assert_eq!(
                chunks.task8_chunk_ranges(),
                vec![(0, chunks.num_coefficients())],
                "the test blob must ride one chunk"
            );
            let bank_bytes = chunks.num_coefficients() as usize * element;
            let narrowed = mutate_fill_plan(&base, first_arm, |bank_first, bytes| {
                let _ = bank_first;
                *bytes -= element;
            });
            census_rejected_by(
                &narrowed,
                first_arm,
                second_arm,
                "coefficient-bank-fill",
                &census_entry(
                    "coefficient_bank",
                    Task8QueuedUse::Write,
                    TASK8_TEST_BANK,
                    bank_bytes - element,
                ),
            );
            families.insert("missing-coefficient-record");

            let moved = mutate_fill_plan(&base, first_arm, |bank_first, bytes| {
                let _ = bytes;
                *bank_first += element;
            });
            census_rejected_by(
                &moved,
                first_arm,
                second_arm,
                "coefficient-bank-fill",
                &census_entry(
                    "coefficient_bank",
                    Task8QueuedUse::Write,
                    TASK8_TEST_BANK + element,
                    bank_bytes,
                ),
            );
            families.insert("inexact-coefficient-record");

            // Every challenge slot the fill's live monomials name, batching and
            // non-batching alike.
            let fill_challenge_slots: Vec<usize> = chunks
                .task8_challenge_slots()
                .iter()
                .flatten()
                .copied()
                .collect();
            for slot in &fill_challenge_slots {
                let target = Task8OmittedRange {
                    arm: first_arm,
                    site: "coefficient-bank-fill",
                    occurrence: 0,
                    use_kind: Task8QueuedUse::Read,
                    address: TASK8_TEST_SLAB + slot * element,
                    bytes: element,
                };
                census_rejected_by(
                    &omit_range(&base, target),
                    first_arm,
                    second_arm,
                    "coefficient-bank-fill",
                    &census_entry(
                        "challenge_slab",
                        Task8QueuedUse::Read,
                        target.address,
                        target.bytes,
                    ),
                );
                families.insert(if *slot == BWD_SEG_CHALLENGE_CLAIM_BATCHING as usize {
                    "missing-challenge-slot"
                } else {
                    "missing-referenced-challenge-slot"
                });
            }

            // The publication pair: the read-back of a published column narrowed
            // to half the column the launch wrote.
            let published = match task8_window_plan(&task8_test_window_descriptor()) {
                Task8EnqueuePlan::Folding { publications, .. } => publications,
                plan => panic!("a window launch plans a fold, not {plan:?}"),
            };
            let (address, bytes) = published[0];
            census_rejected_by(
                &retune_range(
                    &base,
                    Task8OmittedRange {
                        arm: TASK8_WINDOW_ARM,
                        site: "window-launch",
                        occurrence: 0,
                        use_kind: Task8QueuedUse::Read,
                        address,
                        bytes,
                    },
                    address,
                    bytes / 2,
                ),
                first_arm,
                second_arm,
                "window-launch",
                &census_entry("published_column", Task8QueuedUse::Read, address, bytes / 2),
            );
            families.insert("mismatched-publication-pair");

            // The coefficient bank a folding launch reads: exactly the extent
            // the carried symbol declares, not a prefix of it.
            let bank = task8_test_carried().coefficient_bank.unwrap();
            for (arm, site) in [
                (TASK8_WINDOW_ARM, "window-launch"),
                (TASK8_LEGACY_ARM, "segmented-round"),
            ] {
                census_rejected_by(
                    &retune_range(
                        &base,
                        Task8OmittedRange {
                            arm,
                            site,
                            occurrence: 0,
                            use_kind: Task8QueuedUse::Read,
                            address: bank.0,
                            bytes: bank.1,
                        },
                        bank.0,
                        bank.1 - element,
                    ),
                    first_arm,
                    second_arm,
                    site,
                    &census_entry(
                        "ab_gkr_bwd_seg_coeff_bank",
                        Task8QueuedUse::Read,
                        bank.0,
                        bank.1 - element,
                    ),
                );
            }
            families.insert("inexact-coefficient-bank-extent");

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

            assert_eq!(families.len(), 18);
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
            Err(Task8LedgerError::UnownedSpan),
            "a released sub-buffer must not fall back to the allocation it lived in"
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

    let device_inputs = prepare_task8_device_inputs(folding_steps, context)?;
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
    // The host learns the seam's device-squeezed values only through this
    // observation readback; every host oracle below consumes it.
    let master_readback = schedule_read_device_chunked(
        &device_inputs.master[..],
        &mut readback_scratch,
        callbacks,
        context,
        "input-readback",
        |_, _| Vec::new(),
    )?;
    let master_table: Arc<Mutex<Option<Vec<E4>>>> = Arc::new(Mutex::new(None));
    {
        let sink = Arc::clone(&master_table);
        let pending = Mutex::new(Some(master_readback));
        callbacks.schedule(
            move || {
                let values = pending
                    .lock()
                    .expect("Task 8 master readback mutex poisoned")
                    .take()
                    .expect("Task 8 master readback consumed twice")
                    .materialize();
                *sink.lock().expect("Task 8 master table mutex poisoned") = Some(values);
            },
            context.get_exec_stream(),
        )?;
    }
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
            &device_inputs,
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
                &device_inputs,
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
                &device_inputs,
                &mut readback_scratch,
                callbacks,
                context,
                &mut owner_ledger,
                &carried,
            )?;
            let callback_accumulator = Arc::clone(&accumulator);
            let callback_source_table = Arc::clone(&source_table);
            let callback_master_table = Arc::clone(&master_table);
            let callback_folding_steps = folding_steps;
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
                    let master = callback_master_table
                        .lock()
                        .expect("Task 8 master table mutex poisoned")
                        .clone()
                        .expect("Task 8 master observation did not materialize before use");
                    let callback_point_host = master[Task8DeviceInputs::point_offset()..]
                        [..callback_folding_steps + 1]
                        .to_vec();
                    let state = Task8DeviceInputs::point_offset() + callback_folding_steps + 1;
                    assert!(
                        !master[state + 1].is_zero(),
                        "Task 8 device-squeezed Eq prefactor must be invertible"
                    );
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
                    // The Eq readbacks split into covered reads and resident
                    // reads exactly along the union of the arm's real device
                    // producer write spans: one build per pass plus the
                    // comparison build (each writing both high sentinels, its
                    // used group tables, and its low prefix; the finalize
                    // folds rewrite subsets). The expected resident bytes are
                    // derived from that model, so an omitted or shortened
                    // producer span shifts the recorded split away from it —
                    // including the zero at full-coverage coordinates.
                    for (arm, legacy_arm) in
                        [(TASK8_WINDOW_ARM, false), (TASK8_LEGACY_ARM, true)]
                    {
                        assert_eq!(
                            owner_ledger.resident_read_bytes(arm),
                            task8_expected_eq_resident_bytes(
                                callback_folding_steps,
                                start_round,
                                legacy_arm,
                            ),
                            "Task 8 {arm} arm's Eq readbacks disagree with its \
                             recorded device producer coverage"
                        );
                    }
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
                        "Task 8 window arm increased corrected logical peak: window_peak={} legacy_peak={} window_start={:?} legacy_start={:?} window_allocations={:?} legacy_allocations={:?}",
                        window_memory.logical_live_peak_bytes,
                        legacy_memory.logical_live_peak_bytes,
                        window_memory.start,
                        legacy_memory.start,
                        window_allocations,
                        legacy_allocations
                    );
                    let semantic_comparisons = compare_observations(&window, &legacy)
                        .unwrap_or_else(|error| {
                            panic!("Task 8 prepared-state differential mismatch: {error:?}")
                        });
                    let window_eq_build =
                        (start_round + 3, callback_folding_steps - start_round - 3);
                    let legacy_eq_build =
                        (start_round + 1, callback_folding_steps - start_round - 1);
                    for (build, arm, pre, post, post_folds) in [
                        (
                            window_eq_build,
                            "window",
                            &window.pre_eq,
                            &window.post_eq,
                            1usize,
                        ),
                        (
                            legacy_eq_build,
                            "legacy",
                            &legacy.pre_eq,
                            &legacy.post_eq,
                            3usize,
                        ),
                    ] {
                        for (folds, observation) in [(0usize, pre), (post_folds, post)] {
                            validate_arm_eq_observation(
                                &callback_point_host,
                                build.0,
                                build.1,
                                folds,
                                observation,
                            )
                            .unwrap_or_else(|error| {
                                panic!("Task 8 {arm} arm Eq observation mismatch: {error:?}")
                            });
                        }
                    }
                    let mut window_post_coords =
                        task8_eq_coordinates(window_eq_build.0, window_eq_build.1);
                    window_post_coords.fold();
                    let mut legacy_post_coords =
                        task8_eq_coordinates(legacy_eq_build.0, legacy_eq_build.1);
                    for _ in 0..3 {
                        legacy_post_coords.fold();
                    }
                    let expected_remaining: BTreeSet<usize> =
                        (start_round + 4..callback_folding_steps).collect();
                    assert_eq!(
                        window_post_coords.remaining(),
                        expected_remaining,
                        "Task 8 window arm's post-tail Eq coordinate set is wrong"
                    );
                    assert_eq!(
                        legacy_post_coords.remaining(),
                        expected_remaining,
                        "Task 8 legacy arm's post-sequence Eq coordinate set is wrong"
                    );
                    let comparator_field_coverage_checks =
                        run_comparator_field_coverage_checks(&window, &legacy)
                            + run_eq_oracle_coverage_checks(
                                &callback_point_host,
                                window_eq_build.0,
                                window_eq_build.1,
                                &window.pre_eq,
                                &window.post_eq,
                                0,
                                1,
                            )
                            + run_eq_oracle_coverage_checks(
                                &callback_point_host,
                                legacy_eq_build.0,
                                legacy_eq_build.1,
                                &legacy.pre_eq,
                                &legacy.post_eq,
                                0,
                                3,
                            );
                    let mut mutation_checks = 0usize;
                    let (live_mutation_checks, mut mutation_families) =
                        validate_live_observation_mutations(
                            &window,
                            &legacy,
                            (
                                &callback_point_host,
                                window_eq_build.0,
                                window_eq_build.1,
                                1,
                            ),
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
                17 * state.topology_coordinates + 2 * later_coordinates
            );
            assert_eq!(
                state.mutation_checks,
                16 * state.layers + 22 * later_coordinates + 2 * state.multi_source_coordinates
            );
            assert_eq!(
                state.comparator_field_coverage_checks,
                24 * state.topology_coordinates
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
