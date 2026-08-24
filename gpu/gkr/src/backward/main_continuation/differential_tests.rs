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
    eq_group_count, get_eq_high_constant_device_ptr, get_main_layer_claim_point_device_ptr,
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
use crate::backward::vm::production_bind::{
    canonicalize_legacy_publication, family_read_place, prepare_continuation_differential_bank,
    prepare_continuation_differential_rounds, LegacyPublicationCanonicalizationError,
    Task8LivePublicationEvent,
};
use crate::backward::vm::seg::launch_bwd_seg_build_fold_weights;
use crate::backward::vm::seg_coeff_eval::{
    BWD_SEG_CHALLENGE_CLAIM_BATCHING, BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE,
    BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE,
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
const TASK8_PROBE_ARM: &str = "capacity_probe";
const TASK8_SHARED_DEVICE_SYMBOLS: [&str; 2] = ["claim_point_symbol", "eq_high_symbol"];
const TASK8_EQ_RESIDENT_TABLES: &str =
    "factored Eq tables beyond the active groups, read back from the same buffer and symbol by both arms";
const TASK8_NON_PUBLICATION_COMPARISONS: usize =
    12 + 3 + 8 + 1 + 1 + 2 * GKR_EQ_GROUP_TABLE_LEN * (1 + GKR_EQ_HIGH_SLOTS) + 3;

/// One enqueue an arm schedules against a device buffer it owns. `Write` is the
/// enqueue that covers bytes for the first time, `Mutation` overwrites bytes an
/// earlier record already covered, and `Read` copies bytes out or hands them to
/// a launch that only consumes them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8QueuedUse {
    Write,
    Read,
    Mutation,
}

/// What one ledger row states about the byte range it names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8LedgerEntry {
    /// The arm handed exactly this range to one copy or one launch argument.
    Enqueued(Task8QueuedUse),
    /// The arm observes this range without covering it with an enqueue of its
    /// own. The reason names why both arms observe the identical bytes.
    Declared(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8LedgerRecord {
    sequence: u64,
    address: usize,
    range: std::ops::Range<usize>,
    entry: Task8LedgerEntry,
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct Task8OwnerGeneration {
    arm: &'static str,
    label: &'static str,
    owner: usize,
    covered: std::ops::Range<usize>,
    generation: u64,
    superseded_by: Option<u64>,
    initialized: Vec<std::ops::Range<usize>>,
    final_sequence: Option<u64>,
    records: Vec<Task8LedgerRecord>,
}

impl Task8OwnerGeneration {
    fn within(&self, range: &std::ops::Range<usize>) -> bool {
        range.start <= range.end
            && range.start >= self.covered.start
            && range.end <= self.covered.end
    }

    fn holds(coverage: &[std::ops::Range<usize>], range: &std::ops::Range<usize>) -> bool {
        range.start == range.end
            || coverage
                .iter()
                .any(|covered| covered.start <= range.start && range.end <= covered.end)
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

    fn fully_initialized(&self) -> bool {
        self.initialized.len() == 1 && self.initialized[0] == self.covered
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task8LedgerError {
    StaleToken,
    AmbiguousLiveGeneration,
    UseAfterFinal,
    OutOfCoverage,
    UseBeforeInitialization,
    DeclarationOverlapsCoverage,
    ReuseWithoutFinal,
    FinalWithoutUse,
    FinalAlreadyBound,
}

/// Enqueue-order ledger for the device buffers one differential coordinate's
/// arms own. Both arms record here, so a buffer address the second arm receives
/// from the pool, and the two device symbols both arms write, are admitted only
/// as a new generation after the first arm bound `Final` to its exact last use.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Task8OwnerGenerationLedger {
    next_sequence: u64,
    next_generation: u64,
    generations: Vec<Task8OwnerGeneration>,
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

    fn open(
        &mut self,
        arm: &'static str,
        label: &'static str,
        owner: usize,
        bytes: usize,
    ) -> Result<Task8GenerationToken, Task8LedgerError> {
        let covered = owner..owner + bytes;
        match self.live_generation(owner)? {
            None => Ok(self.register(arm, label, covered)),
            Some(prior) => self.admit_reuse(arm, label, prior, covered),
        }
    }

    fn register(
        &mut self,
        arm: &'static str,
        label: &'static str,
        covered: std::ops::Range<usize>,
    ) -> Task8GenerationToken {
        self.next_generation += 1;
        let token = Task8GenerationToken {
            slot: self.generations.len(),
            owner: covered.start,
            generation: self.next_generation,
        };
        self.generations.push(Task8OwnerGeneration {
            arm,
            label,
            owner: covered.start,
            covered,
            generation: self.next_generation,
            superseded_by: None,
            initialized: Vec::new(),
            final_sequence: None,
            records: Vec::new(),
        });
        token
    }

    /// The only admission a repeated owner address has. The caller names the
    /// generation it is retiring; that generation must still be the open one and
    /// must have bound `Final` to its own last enqueue, so no queued use of it
    /// can remain. The successor starts with no coverage of its own, so it can
    /// read nothing the retired generation left behind.
    fn admit_reuse(
        &mut self,
        arm: &'static str,
        label: &'static str,
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
                .final_sequence
                .ok_or(Task8LedgerError::ReuseWithoutFinal)?;
            if entry.records.last().map(|record| record.sequence) != Some(bound) {
                return Err(Task8LedgerError::ReuseWithoutFinal);
            }
        }
        let token = self.register(arm, label, covered);
        self.generations[slot].superseded_by = Some(token.generation);
        Ok(token)
    }

    fn enqueue(
        &mut self,
        token: Task8GenerationToken,
        address: usize,
        bytes: usize,
        use_kind: Task8QueuedUse,
    ) -> Result<u64, Task8LedgerError> {
        let slot = self.resolve(token)?;
        let range = address..address + bytes;
        {
            let entry = &self.generations[slot];
            if entry.final_sequence.is_some() || entry.superseded_by.is_some() {
                return Err(Task8LedgerError::UseAfterFinal);
            }
            if !entry.within(&range) {
                return Err(Task8LedgerError::OutOfCoverage);
            }
            if use_kind != Task8QueuedUse::Write
                && !Task8OwnerGeneration::holds(&entry.initialized, &range)
            {
                return Err(Task8LedgerError::UseBeforeInitialization);
            }
        }
        let sequence = self.next_sequence;
        self.next_sequence += 1;
        let entry = &mut self.generations[slot];
        if use_kind == Task8QueuedUse::Write {
            Task8OwnerGeneration::absorb(&mut entry.initialized, range.clone());
        }
        entry.records.push(Task8LedgerRecord {
            sequence,
            address,
            range,
            entry: Task8LedgerEntry::Enqueued(use_kind),
        });
        Ok(sequence)
    }

    /// Adds coverage the arm did not enqueue itself. It is admitted only for
    /// bytes no record of this generation already covers, so it can never
    /// restate an enqueue or stand in for a missing one.
    fn declare_initialized(
        &mut self,
        token: Task8GenerationToken,
        address: usize,
        bytes: usize,
        reason: &'static str,
    ) -> Result<u64, Task8LedgerError> {
        let slot = self.resolve(token)?;
        let range = address..address + bytes;
        {
            let entry = &self.generations[slot];
            if entry.final_sequence.is_some() || entry.superseded_by.is_some() {
                return Err(Task8LedgerError::UseAfterFinal);
            }
            if !entry.within(&range) || range.start == range.end {
                return Err(Task8LedgerError::OutOfCoverage);
            }
            if entry
                .initialized
                .iter()
                .any(|covered| covered.start < range.end && range.start < covered.end)
            {
                return Err(Task8LedgerError::DeclarationOverlapsCoverage);
            }
        }
        let sequence = self.next_sequence;
        self.next_sequence += 1;
        let entry = &mut self.generations[slot];
        Task8OwnerGeneration::absorb(&mut entry.initialized, range.clone());
        entry.records.push(Task8LedgerRecord {
            sequence,
            address,
            range,
            entry: Task8LedgerEntry::Declared(reason),
        });
        Ok(sequence)
    }

    /// Binds `Final` to the generation's own last enqueue. Every later
    /// operation on that generation is rejected, which is what a queued use of a
    /// reused address reduces to.
    fn bind_final(&mut self, token: Task8GenerationToken) -> Result<u64, Task8LedgerError> {
        let slot = self.resolve(token)?;
        let entry = &mut self.generations[slot];
        if entry.final_sequence.is_some() {
            return Err(Task8LedgerError::FinalAlreadyBound);
        }
        let last = entry
            .records
            .last()
            .ok_or(Task8LedgerError::FinalWithoutUse)?;
        if !matches!(last.entry, Task8LedgerEntry::Enqueued(_)) {
            return Err(Task8LedgerError::FinalWithoutUse);
        }
        let bound = last.sequence;
        entry.final_sequence = Some(bound);
        Ok(bound)
    }

    fn generation(&self, token: Task8GenerationToken) -> &Task8OwnerGeneration {
        &self.generations[self.resolve(token).expect("Task 8 ledger token is stale")]
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

    fn labelled(&self, label: &'static str) -> Vec<&Task8OwnerGeneration> {
        self.generations
            .iter()
            .filter(|entry| entry.label == label)
            .collect()
    }
}

/// One owner the arm holds open: the token plus the element geometry every
/// record's address and byte range is derived from.
#[derive(Clone, Copy, Debug)]
struct Task8LedgerOwner {
    token: Task8GenerationToken,
    arm: &'static str,
    label: &'static str,
    base: usize,
    elem_bytes: usize,
    elems: usize,
}

fn ledger_open_raw(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    label: &'static str,
    base: usize,
    elem_bytes: usize,
    elems: usize,
) -> Task8LedgerOwner {
    let token = ledger
        .open(arm, label, base, elems * elem_bytes)
        .unwrap_or_else(|error| panic!("Task 8 {arm} arm could not open {label}: {error:?}"));
    Task8LedgerOwner {
        token,
        arm,
        label,
        base,
        elem_bytes,
        elems,
    }
}

fn ledger_open<T>(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    label: &'static str,
    allocation: &DeviceSlice<T>,
) -> Task8LedgerOwner {
    ledger_open_raw(
        ledger,
        arm,
        label,
        allocation.as_ptr() as usize,
        std::mem::size_of::<T>(),
        allocation.len(),
    )
}

fn ledger_note(
    ledger: &mut Task8OwnerGenerationLedger,
    owner: &Task8LedgerOwner,
    offset: usize,
    elems: usize,
    use_kind: Task8QueuedUse,
) -> u64 {
    let address = owner.base + offset * owner.elem_bytes;
    ledger
        .enqueue(owner.token, address, elems * owner.elem_bytes, use_kind)
        .unwrap_or_else(|error| {
            let (arm, label) = (owner.arm, owner.label);
            panic!(
                "Task 8 {arm} arm {use_kind:?} of {label}[{offset}..{offset}+{elems}]: {error:?}"
            )
        })
}

/// Declares every byte of `owner` no record of its open generation covers yet.
fn ledger_declare_remaining(
    ledger: &mut Task8OwnerGenerationLedger,
    owner: &Task8LedgerOwner,
    reason: &'static str,
) -> usize {
    let entry = ledger.generation(owner.token);
    let covered = entry.covered.clone();
    let mut gaps = Vec::new();
    let mut cursor = covered.start;
    for held in entry.initialized.clone() {
        if held.start > cursor {
            gaps.push(cursor..held.start);
        }
        cursor = cursor.max(held.end);
    }
    if cursor < covered.end {
        gaps.push(cursor..covered.end);
    }
    for gap in &gaps {
        ledger
            .declare_initialized(owner.token, gap.start, gap.end - gap.start, reason)
            .unwrap_or_else(|error| {
                let (arm, label) = (owner.arm, owner.label);
                panic!("Task 8 {arm} arm could not declare the remainder of {label}: {error:?}")
            });
    }
    gaps.len()
}

fn ledger_bind_final(ledger: &mut Task8OwnerGenerationLedger, owner: &Task8LedgerOwner) -> u64 {
    ledger.bind_final(owner.token).unwrap_or_else(|error| {
        let (arm, label) = (owner.arm, owner.label);
        panic!("Task 8 {arm} arm could not bind Final to {label}: {error:?}")
    })
}

/// Records the in-place fold of the active Eq slot against whichever owner the
/// resolved slot base belongs to: the low buffer, or one of the two high slabs.
fn ledger_note_active_eq_slot(
    ledger: &mut Task8OwnerGenerationLedger,
    eq_low: &Task8LedgerOwner,
    eq_high: &Task8LedgerOwner,
    base: *mut E4,
    size_before_fold: u32,
) {
    let base = base as usize;
    let owner = if base >= eq_low.base && base < eq_low.base + eq_low.elems * eq_low.elem_bytes {
        eq_low
    } else {
        eq_high
    };
    assert!(
        base >= owner.base,
        "Task 8 active Eq slot resolved outside both Eq owners"
    );
    let offset = (base - owner.base) / owner.elem_bytes;
    let elems = if size_before_fold == 0 {
        0
    } else {
        1usize << size_before_fold
    };
    ledger_note(ledger, owner, offset, elems, Task8QueuedUse::Mutation);
}

/// Replays a coordinate's ledger: every record is checked against the coverage
/// its own generation held when that record was made, `Final` is checked against
/// the generation's exact last enqueue, and each shared device symbol is checked
/// for the two-arm generation transition. Returns the confirmed transitions.
fn validate_owner_generation_ledger(
    ledger: &Task8OwnerGenerationLedger,
    first_arm: &'static str,
    second_arm: &'static str,
    shared_symbols: &[&'static str],
) -> usize {
    assert!(
        !ledger.generations.is_empty(),
        "Task 8 ledger recorded no owner generation"
    );
    let mut sequences = Vec::new();
    for entry in &ledger.generations {
        assert!(
            entry.arm == first_arm || entry.arm == second_arm,
            "Task 8 ledger generation {} came from an unexpected arm {}",
            entry.generation,
            entry.arm
        );
        let mut coverage: Vec<std::ops::Range<usize>> = Vec::new();
        let mut previous = None;
        for record in &entry.records {
            if let Some(previous) = previous {
                assert!(
                    record.sequence > previous,
                    "Task 8 ledger records for {} are out of enqueue order",
                    entry.label
                );
            }
            previous = Some(record.sequence);
            sequences.push(record.sequence);
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
            match record.entry {
                Task8LedgerEntry::Enqueued(Task8QueuedUse::Write) => {
                    Task8OwnerGeneration::absorb(&mut coverage, record.range.clone());
                }
                Task8LedgerEntry::Enqueued(_) => assert!(
                    Task8OwnerGeneration::holds(&coverage, &record.range),
                    "Task 8 {} used bytes its generation had not covered",
                    entry.label
                ),
                Task8LedgerEntry::Declared(_) => {
                    assert!(
                        !Task8OwnerGeneration::holds(&coverage, &record.range),
                        "Task 8 {} declared bytes an enqueue already covered",
                        entry.label
                    );
                    Task8OwnerGeneration::absorb(&mut coverage, record.range.clone());
                }
            }
        }
        assert_eq!(
            coverage, entry.initialized,
            "Task 8 {} coverage replay disagrees with the ledger",
            entry.label
        );
        let bound = entry
            .final_sequence
            .unwrap_or_else(|| panic!("Task 8 {} never bound Final", entry.label));
        let last = entry
            .records
            .last()
            .unwrap_or_else(|| panic!("Task 8 {} bound Final without a use", entry.label));
        assert_eq!(
            bound, last.sequence,
            "Task 8 {} bound Final away from its last use",
            entry.label
        );
        assert!(
            matches!(last.entry, Task8LedgerEntry::Enqueued(_)),
            "Task 8 {} bound Final to a declaration",
            entry.label
        );
    }
    sequences.sort_unstable();
    assert_eq!(
        sequences.len() as u64,
        ledger.next_sequence,
        "Task 8 ledger sequence count and record count disagree"
    );
    assert!(
        sequences
            .iter()
            .enumerate()
            .all(|(index, sequence)| index as u64 == *sequence),
        "Task 8 ledger sequence numbers are not the dense enqueue order"
    );
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
            first.final_sequence.unwrap() < second.records[0].sequence,
            "Task 8 shared symbol {label} reused an address before its Final"
        );
        assert!(
            first.fully_initialized(),
            "Task 8 shared symbol {label} was reused without full coverage"
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

fn upload<T: Copy>(
    context: &ProverContext,
    host: &[T],
) -> CudaResult<(DeviceAllocation<T>, StaticPinnedBox<T>)> {
    let staging = alloc_static_pinned_box_from_slice(host)?;
    let mut device = context.alloc(host.len().max(1), AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut device[..host.len()],
        &staging[..],
        context.get_exec_stream(),
    )?;
    Ok((device, staging))
}

fn write_claim_point_symbol(
    context: &ProverContext,
    point: &[E4],
) -> CudaResult<StaticPinnedBox<E4>> {
    let staging = alloc_static_pinned_box_from_slice(point)?;
    // SAFETY: the main-layer claim-point symbol is sized for every admitted
    // folding width; the corpus maximum is pinned independently by preflight.
    let destination = unsafe {
        DeviceSlice::from_raw_parts_mut(get_main_layer_claim_point_device_ptr(), point.len())
    };
    memory_copy_async(destination, &staging[..], context.get_exec_stream())?;
    Ok(staging)
}

fn schedule_read_device_chunked<T>(
    source: &DeviceSlice<T>,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledReadback<T>>
where
    T: Copy + Default + Send + Sync + 'static,
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
        memory_copy_async(
            host_chunk,
            &source[offset..offset + len],
            context.get_exec_stream(),
        )?;
        let callback_output = Arc::clone(&output);
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

fn schedule_read_all_eq(
    sizes: GkrEqSizes,
    eq_low: &DeviceAllocation<E4>,
    scratch: &mut StaticPinnedBox<u8>,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<ScheduledEqObservation> {
    // SAFETY: the high Eq symbol is a contiguous two-table device region.
    let high = unsafe {
        DeviceSlice::from_raw_parts(
            get_eq_high_constant_device_ptr() as *const E4,
            GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
        )
    };
    Ok(ScheduledEqObservation {
        sizes,
        low: schedule_read_device_chunked(eq_low, scratch, callbacks, context)?,
        high: schedule_read_device_chunked(high, scratch, callbacks, context)?,
    })
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

fn retain_in_callback<T: Send + Sync + 'static>(
    value: T,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    callbacks.schedule(
        move || {
            let _ = &value;
        },
        context.get_exec_stream(),
    )
}

fn schedule_live_device_mutation<T>(
    family: &'static str,
    target: Task8LiveMutationTarget,
    destination: *mut T,
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
    let staging = alloc_static_pinned_box_from_slice(&[value])?;
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(destination, 1) };
    memory_copy_async(destination, &staging[..], context.get_exec_stream())?;
    let readback = schedule_read_device_chunked(destination, readback_scratch, callbacks, context)?;
    retain_in_callback(staging, callbacks, context)?;
    Ok((family, target, value, readback))
}

/// The owners every main-continuation pass names, in either arm.
#[derive(Clone, Copy, Debug)]
struct Task8PassOwners {
    arm: &'static str,
    claim_point: Task8LedgerOwner,
    claim_point_symbol: Task8LedgerOwner,
    eq_low: Task8LedgerOwner,
    eq_high: Task8LedgerOwner,
    partials: Task8LedgerOwner,
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

/// The claim-point coordinates one Eq build reads and the group tables it
/// writes: the last group lands in the low buffer, every earlier group fills one
/// whole high slab, and thread 0 of both high blocks seeds its slot's first
/// entry.
fn record_eq_build(
    ledger: &mut Task8OwnerGenerationLedger,
    owners: &Task8PassOwners,
    folding_steps: usize,
    pass_start: usize,
) {
    let challenge_offset = pass_start + 3;
    let challenge_count = folding_steps - pass_start - 3;
    ledger_note(
        ledger,
        &owners.claim_point,
        challenge_offset,
        challenge_count,
        Task8QueuedUse::Read,
    );
    for slot in 0..GKR_EQ_HIGH_SLOTS {
        ledger_note(
            ledger,
            &owners.eq_high,
            slot * GKR_EQ_GROUP_TABLE_LEN,
            1,
            Task8QueuedUse::Write,
        );
    }
    for group in 0..eq_group_count(challenge_count).saturating_sub(1) {
        ledger_note(
            ledger,
            &owners.eq_high,
            group * GKR_EQ_GROUP_TABLE_LEN,
            GKR_EQ_GROUP_TABLE_LEN,
            Task8QueuedUse::Write,
        );
    }
    ledger_note(
        ledger,
        &owners.eq_low,
        0,
        active_eq_low_table(challenge_count),
        Task8QueuedUse::Write,
    );
}

fn active_eq_low_table(challenge_count: usize) -> usize {
    1usize << make_eq_sizes(challenge_count).low
}

/// The main-layer claim-point coordinates the fold-weight build reads: every
/// depth it folds is bounded by the round it builds for.
fn record_fold_weights(
    ledger: &mut Task8OwnerGenerationLedger,
    owners: &Task8PassOwners,
    round: usize,
) {
    ledger_note(
        ledger,
        &owners.claim_point_symbol,
        0,
        round,
        Task8QueuedUse::Read,
    );
}

/// The buffers one window launch names: the active Eq table it folds against,
/// the prior published level it consumes, the row-tile partial matrix it fills,
/// and the level it publishes.
fn record_window_launch(
    ledger: &mut Task8OwnerGenerationLedger,
    owners: &Task8PassOwners,
    folding_steps: usize,
    pass_start: usize,
    prior: Option<&Task8LedgerOwner>,
    row_tiles: usize,
    publication: &Task8LedgerOwner,
) {
    ledger_note(
        ledger,
        &owners.eq_low,
        0,
        active_eq_low_table(folding_steps - pass_start - 3),
        Task8QueuedUse::Read,
    );
    if let Some(prior) = prior {
        ledger_note(ledger, prior, 0, prior.elems, Task8QueuedUse::Read);
    }
    ledger_note(
        ledger,
        &owners.partials,
        0,
        MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * row_tiles,
        Task8QueuedUse::Write,
    );
    ledger_note(
        ledger,
        publication,
        0,
        publication.elems,
        Task8QueuedUse::Write,
    );
}

/// The challenge slab fill both arms share: the external prefix copy, the three
/// single-slot copies, and the coefficient-bank evaluation that reads the slab.
fn record_bank_fill(
    ledger: &mut Task8OwnerGenerationLedger,
    slab: &Task8LedgerOwner,
    external: &Task8LedgerOwner,
    lookup_multiplicative: &Task8LedgerOwner,
    lookup_additive: &Task8LedgerOwner,
    claim_batching: &Task8LedgerOwner,
) {
    let prefix = BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE as usize;
    ledger_note(ledger, external, 0, prefix, Task8QueuedUse::Read);
    ledger_note(ledger, slab, 0, prefix, Task8QueuedUse::Write);
    for (slot, source) in [
        (
            BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE,
            lookup_multiplicative,
        ),
        (BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE, lookup_additive),
        (BWD_SEG_CHALLENGE_CLAIM_BATCHING, claim_batching),
    ] {
        ledger_note(ledger, source, 0, 1, Task8QueuedUse::Read);
        ledger_note(ledger, slab, slot as usize, 1, Task8QueuedUse::Write);
    }
    ledger_note(ledger, slab, 0, slab.elems, Task8QueuedUse::Read);
}

fn open_challenge_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    external: &DeviceAllocation<E4>,
    lookup_multiplicative: &DeviceAllocation<E4>,
    lookup_additive: &DeviceAllocation<E4>,
    claim_batching: &DeviceAllocation<E4>,
) -> Task8ChallengeOwners {
    let mut open = |label, allocation| {
        let owner = ledger_open(ledger, arm, label, allocation);
        ledger_note(ledger, &owner, 0, owner.elems, Task8QueuedUse::Write);
        owner
    };
    Task8ChallengeOwners {
        external: open("external_challenges", external),
        lookup_multiplicative: open("lookup_multiplicative", lookup_multiplicative),
        lookup_additive: open("lookup_additive", lookup_additive),
        claim_batching: open("claim_batching", claim_batching),
    }
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

/// The resident Eq regions one arm declares once: the low buffer's tail beyond
/// the widest active table any of its passes built, and each high slab no pass
/// filled.
/// Every owner one arm opens at one coordinate. `prior_publication` appears
/// only where a pass before the compared one published.
fn expected_arm_owner_labels(start_round: usize) -> BTreeSet<&'static str> {
    let mut labels = BTreeSet::from([
        "challenge_slab",
        "challenges",
        "claim_batching",
        "claim_point",
        "claim_point_symbol",
        "coefficients",
        "eq",
        "eq_high_symbol",
        "external_challenges",
        "lookup_additive",
        "lookup_multiplicative",
        "partials",
        "publication",
        "transcript_claim",
        "transcript_prefactor",
        "transcript_seed",
    ]);
    if start_round > 3 {
        labels.insert("prior_publication");
    }
    labels
}

fn expected_declared_eq_regions(folding_steps: usize, start_round: usize) -> usize {
    let mut low = 0usize;
    let mut high_slabs = 0usize;
    for pass_start in (3..=start_round).step_by(3) {
        let challenge_count = folding_steps - pass_start - 3;
        low = low.max(active_eq_low_table(challenge_count));
        high_slabs = high_slabs.max(eq_group_count(challenge_count).saturating_sub(1));
    }
    usize::from(low < GKR_EQ_GROUP_TABLE_LEN) + GKR_EQ_HIGH_SLOTS.saturating_sub(high_slabs)
}

fn open_transcript_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    transcript: &TranscriptBuffers,
) -> Task8TranscriptOwners {
    let seed = ledger_open(ledger, arm, "transcript_seed", &transcript.seed);
    ledger_note(ledger, &seed, 0, seed.elems, Task8QueuedUse::Write);
    let claim = ledger_open(ledger, arm, "transcript_claim", &transcript.claim);
    ledger_note(ledger, &claim, 0, claim.elems, Task8QueuedUse::Write);
    let prefactor = ledger_open(ledger, arm, "transcript_prefactor", &transcript.prefactor);
    ledger_note(
        ledger,
        &prefactor,
        0,
        prefactor.elems,
        Task8QueuedUse::Write,
    );
    Task8TranscriptOwners {
        seed,
        claim,
        prefactor,
        coefficients: ledger_open(ledger, arm, "coefficients", &transcript.coefficients),
        challenges: ledger_open(ledger, arm, "challenges", &transcript.challenges),
    }
}

/// The transcript state one finalize advances in place and the exact coefficient
/// and challenge slots it writes out.
fn record_transcript_finalize(
    ledger: &mut Task8OwnerGenerationLedger,
    transcript: &Task8TranscriptOwners,
    coefficients: std::ops::Range<usize>,
    challenges: std::ops::Range<usize>,
) {
    for owner in [&transcript.seed, &transcript.claim, &transcript.prefactor] {
        ledger_note(ledger, owner, 0, owner.elems, Task8QueuedUse::Read);
        ledger_note(ledger, owner, 0, owner.elems, Task8QueuedUse::Mutation);
    }
    ledger_note(
        ledger,
        &transcript.coefficients,
        coefficients.start,
        coefficients.end - coefficients.start,
        Task8QueuedUse::Write,
    );
    ledger_note(
        ledger,
        &transcript.challenges,
        challenges.start,
        challenges.end - challenges.start,
        Task8QueuedUse::Write,
    );
}

fn record_transcript_readbacks(
    ledger: &mut Task8OwnerGenerationLedger,
    transcript: &Task8TranscriptOwners,
) {
    for owner in [
        &transcript.coefficients,
        &transcript.challenges,
        &transcript.seed,
        &transcript.claim,
        &transcript.prefactor,
    ] {
        ledger_note(ledger, owner, 0, owner.elems, Task8QueuedUse::Read);
    }
}

/// One whole-buffer Eq readback. The bytes beyond the active groups are the
/// tables' resident content, which both arms read back from the same buffer and
/// the same symbol, so the arm declares them instead of covering them.
fn record_eq_readback(ledger: &mut Task8OwnerGenerationLedger, owners: &Task8PassOwners) -> usize {
    let declared = ledger_declare_remaining(ledger, &owners.eq_low, TASK8_EQ_RESIDENT_TABLES)
        + ledger_declare_remaining(ledger, &owners.eq_high, TASK8_EQ_RESIDENT_TABLES);
    ledger_note(
        ledger,
        &owners.eq_low,
        0,
        owners.eq_low.elems,
        Task8QueuedUse::Read,
    );
    ledger_note(
        ledger,
        &owners.eq_high,
        0,
        owners.eq_high.elems,
        Task8QueuedUse::Read,
    );
    declared
}

/// One live device mutation: the single-cell overwrite and the readback that
/// observes it.
fn record_live_mutation(
    ledger: &mut Task8OwnerGenerationLedger,
    owner: &Task8LedgerOwner,
    offset: usize,
) {
    ledger_note(ledger, owner, offset, 1, Task8QueuedUse::Mutation);
    ledger_note(ledger, owner, offset, 1, Task8QueuedUse::Read);
}

/// Base addresses of the buffers and symbols one pass names.
#[derive(Clone, Copy, Debug)]
struct Task8PassAddresses {
    claim_point: usize,
    point_len: usize,
    claim_point_symbol: usize,
    eq_low: usize,
    eq_high: usize,
    partials: usize,
    partials_len: usize,
}

fn pass_addresses(
    claim_point: &DeviceAllocation<E4>,
    point_len: usize,
    eq_low: &DeviceAllocation<E4>,
    partials: &DeviceAllocation<E4>,
) -> Task8PassAddresses {
    Task8PassAddresses {
        claim_point: claim_point.as_ptr() as usize,
        point_len,
        claim_point_symbol: get_main_layer_claim_point_device_ptr() as usize,
        eq_low: eq_low.as_ptr() as usize,
        eq_high: get_eq_high_constant_device_ptr() as usize,
        partials: partials.as_ptr() as usize,
        partials_len: partials.len(),
    }
}

/// Opens the buffers and the two device symbols a pass names, and records the
/// claim-point upload and the symbol write both arms schedule first.
fn open_pass_owners(
    ledger: &mut Task8OwnerGenerationLedger,
    arm: &'static str,
    addresses: Task8PassAddresses,
) -> Task8PassOwners {
    let elem_bytes = std::mem::size_of::<E4>();
    let claim_point = ledger_open_raw(
        ledger,
        arm,
        "claim_point",
        addresses.claim_point,
        elem_bytes,
        addresses.point_len,
    );
    ledger_note(
        ledger,
        &claim_point,
        0,
        addresses.point_len,
        Task8QueuedUse::Write,
    );
    let claim_point_symbol = ledger_open_raw(
        ledger,
        arm,
        "claim_point_symbol",
        addresses.claim_point_symbol,
        elem_bytes,
        addresses.point_len,
    );
    ledger_note(
        ledger,
        &claim_point_symbol,
        0,
        addresses.point_len,
        Task8QueuedUse::Write,
    );
    Task8PassOwners {
        arm,
        claim_point,
        claim_point_symbol,
        eq_low: ledger_open_raw(
            ledger,
            arm,
            "eq",
            addresses.eq_low,
            elem_bytes,
            GKR_EQ_GROUP_TABLE_LEN,
        ),
        eq_high: ledger_open_raw(
            ledger,
            arm,
            "eq_high_symbol",
            addresses.eq_high,
            elem_bytes,
            GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
        ),
        partials: ledger_open_raw(
            ledger,
            arm,
            "partials",
            addresses.partials,
            elem_bytes,
            addresses.partials_len,
        ),
    }
}

fn bind_pass_owners_final(ledger: &mut Task8OwnerGenerationLedger, owners: &Task8PassOwners) {
    for owner in [
        &owners.claim_point,
        &owners.eq_low,
        &owners.partials,
        &owners.claim_point_symbol,
        &owners.eq_high,
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
    owners: &Task8PassOwners,
) -> CudaResult<(Option<ContinuationPublishedLevel>, Option<Task8LedgerOwner>)> {
    let mut prior = None;
    let mut prior_owner: Option<Task8LedgerOwner> = None;
    for pass_start in (3..target_start).step_by(3) {
        launch_build_eq_high_and_low_groups_from_point(
            claim_point,
            pass_start + 3,
            folding_steps - pass_start - 3,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        record_eq_build(ledger, owners, folding_steps, pass_start);
        launch_bwd_seg_build_fold_weights(pass_start as u32, context)?;
        record_fold_weights(ledger, owners, pass_start);
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
        let published = ledger_open(
            ledger,
            owners.arm,
            "prior_publication",
            launched.published_level().allocation(),
        );
        record_window_launch(
            ledger,
            owners,
            folding_steps,
            pass_start,
            prior_owner.as_ref(),
            launched.row_tiles(),
            &published,
        );
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
) -> CudaResult<ScheduledPreparedObservation> {
    let interval_entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (mut observation, allocations, declared_eq_tables) = {
        let mut allocations = Vec::new();
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_symbol_staging = write_claim_point_symbol(context, point_host)?;
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
        let owners = open_pass_owners(
            ledger,
            TASK8_WINDOW_ARM,
            pass_addresses(&claim_point, point_host.len(), &eq_low, &partials),
        );
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
        let slab = ledger_open(
            ledger,
            TASK8_WINDOW_ARM,
            "challenge_slab",
            bank.challenge_slab(),
        );
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, external_staging) = upload(context, &external_host)?;
        let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
        let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
        let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
        let challenge_owners = open_challenge_owners(
            ledger,
            TASK8_WINDOW_ARM,
            &external,
            &lookup_mul,
            &lookup_add,
            &batching,
        );
        bank.schedule(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        record_bank_fill(
            ledger,
            &slab,
            &challenge_owners.external,
            &challenge_owners.lookup_multiplicative,
            &challenge_owners.lookup_additive,
            &challenge_owners.claim_batching,
        );

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
            &owners,
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
        let prior_original = prior
            .as_ref()
            .map(|prior| {
                let first = unsafe { DeviceSlice::from_raw_parts(prior.allocation().as_ptr(), 1) };
                schedule_read_device_chunked(first, readback_scratch, callbacks, context)
            })
            .transpose()?;
        if let Some(prior_owner) = prior_owner.as_ref() {
            ledger_note(ledger, prior_owner, 0, 1, Task8QueuedUse::Read);
        }
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            start_round + 3,
            folding_steps - start_round - 3,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        record_eq_build(ledger, &owners, folding_steps, start_round);
        launch_bwd_seg_build_fold_weights(start_round as u32, context)?;
        record_fold_weights(ledger, &owners, start_round);
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
        let publication_owner = ledger_open(
            ledger,
            TASK8_WINDOW_ARM,
            "publication",
            launched.published_level().allocation(),
        );
        record_window_launch(
            ledger,
            &owners,
            folding_steps,
            start_round,
            prior_owner.as_ref(),
            launched.row_tiles(),
            &publication_owner,
        );
        let pre_sizes = launched.eq_sizes();
        let pre_eq =
            schedule_read_all_eq(pre_sizes, &eq_low, readback_scratch, callbacks, context)?;
        let declared_eq_tables = record_eq_readback(ledger, &owners);
        let mut transcript = transcript_buffers(context)?;
        allocations.append(&mut transcript.allocations);
        let transcript_owners = open_transcript_owners(ledger, TASK8_WINDOW_ARM, &transcript);
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
        let row_tiles = launched.row_tiles();
        let tensor_base = MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * row_tiles;
        ledger_note(
            ledger,
            &owners.partials,
            0,
            tensor_base,
            Task8QueuedUse::Read,
        );
        ledger_note(
            ledger,
            &owners.partials,
            tensor_base,
            MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
            Task8QueuedUse::Write,
        );
        ledger_note(
            ledger,
            &owners.partials,
            tensor_base,
            MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
            Task8QueuedUse::Read,
        );
        ledger_note(
            ledger,
            &owners.claim_point,
            start_round,
            3,
            Task8QueuedUse::Read,
        );
        record_transcript_finalize(ledger, &transcript_owners, 0..12, 0..3);
        ledger_note_active_eq_slot(
            ledger,
            &owners.eq_low,
            &owners.eq_high,
            active_eq_slot_base,
            active_eq_size_before_fold,
        );
        let mut post_sizes = pre_sizes;
        record_active_eq_slot_fold(&mut post_sizes);
        let publication = schedule_read_device_chunked(
            launched.published_level().allocation(),
            readback_scratch,
            callbacks,
            context,
        )?;
        ledger_note(
            ledger,
            &publication_owner,
            0,
            publication_owner.elems,
            Task8QueuedUse::Read,
        );
        let coefficients = schedule_read_device_chunked(
            &transcript.coefficients,
            readback_scratch,
            callbacks,
            context,
        )?;
        let challenges = schedule_read_device_chunked(
            &transcript.challenges,
            readback_scratch,
            callbacks,
            context,
        )?;
        let seed =
            schedule_read_device_chunked(&transcript.seed, readback_scratch, callbacks, context)?;
        let claim =
            schedule_read_device_chunked(&transcript.claim, readback_scratch, callbacks, context)?;
        let eq_prefactor = schedule_read_device_chunked(
            &transcript.prefactor,
            readback_scratch,
            callbacks,
            context,
        )?;
        record_transcript_readbacks(ledger, &transcript_owners);
        let post_eq =
            schedule_read_all_eq(post_sizes, &eq_low, readback_scratch, callbacks, context)?;
        assert_eq!(
            record_eq_readback(ledger, &owners),
            0,
            "Task 8 window arm left Eq bytes uncovered after the first readback"
        );
        let boundary =
            main_continuation_post_tail_eq_boundary(start_round as u8, folding_steps, post_sizes);
        let mut live_mutations = ScheduledLiveMutationEvidence::empty();
        live_mutations.prior_original = prior_original;
        live_mutations.e4.push(schedule_live_device_mutation(
            "window-publication-lane",
            Task8LiveMutationTarget::Publication(0),
            launched.published_level().allocation().as_ptr() as *mut E4,
            deterministic_e4(0x981),
            readback_scratch,
            callbacks,
            context,
        )?);
        record_live_mutation(ledger, &publication_owner, 0);
        for (index, tag) in [(0usize, 0x982), (4, 0x983), (8, 0x984)] {
            live_mutations.e4.push(schedule_live_device_mutation(
                "axis-product-infinity-coefficients",
                Task8LiveMutationTarget::Coefficient(index),
                unsafe { transcript.coefficients.as_mut_ptr().add(index) },
                deterministic_e4(tag),
                readback_scratch,
                callbacks,
                context,
            )?);
            record_live_mutation(ledger, &transcript_owners.coefficients, index);
        }
        live_mutations.e4.push(schedule_live_device_mutation(
            "row-weight",
            Task8LiveMutationTarget::Coefficient(1),
            unsafe { transcript.coefficients.as_mut_ptr().add(1) },
            deterministic_e4(0x985),
            readback_scratch,
            callbacks,
            context,
        )?);
        record_live_mutation(ledger, &transcript_owners.coefficients, 1);
        for (index, tag) in [(0usize, 0x986), (1, 0x987), (2, 0x988)] {
            live_mutations.e4.push(schedule_live_device_mutation(
                "challenges",
                Task8LiveMutationTarget::Challenge(index),
                unsafe { transcript.challenges.as_mut_ptr().add(index) },
                deterministic_e4(tag),
                readback_scratch,
                callbacks,
                context,
            )?);
            record_live_mutation(ledger, &transcript_owners.challenges, index);
        }
        live_mutations.u32.push(schedule_live_device_mutation(
            "transcript-seed",
            Task8LiveMutationTarget::Seed(0),
            transcript.seed.as_mut_ptr(),
            0xa5a5_5a5a,
            readback_scratch,
            callbacks,
            context,
        )?);
        record_live_mutation(ledger, &transcript_owners.seed, 0);
        live_mutations.e4.push(schedule_live_device_mutation(
            "claim",
            Task8LiveMutationTarget::Claim(0),
            transcript.claim.as_mut_ptr(),
            deterministic_e4(0x989),
            readback_scratch,
            callbacks,
            context,
        )?);
        record_live_mutation(ledger, &transcript_owners.claim, 0);
        live_mutations.e4.push(schedule_live_device_mutation(
            "eq-prefactor",
            Task8LiveMutationTarget::EqPrefactor(0),
            transcript.prefactor.as_mut_ptr(),
            deterministic_e4(0x98a),
            readback_scratch,
            callbacks,
            context,
        )?);
        record_live_mutation(ledger, &transcript_owners.prefactor, 0);
        live_mutations.e4.push(schedule_live_device_mutation(
            "stale-eq",
            Task8LiveMutationTarget::PostEqLow(0),
            eq_low.as_mut_ptr(),
            deterministic_e4(0x98b),
            readback_scratch,
            callbacks,
            context,
        )?);
        record_live_mutation(ledger, &owners.eq_low, 0);
        if let Some(prior) = prior.as_ref() {
            live_mutations.e4.push(schedule_live_device_mutation(
                "prior-publication-cell",
                Task8LiveMutationTarget::PriorPublication,
                prior.allocation().as_ptr() as *mut E4,
                deterministic_e4(0x98c),
                readback_scratch,
                callbacks,
                context,
            )?);
        }
        if let Some(prior_owner) = prior_owner.as_ref() {
            record_live_mutation(ledger, prior_owner, 0);
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
        ledger_bind_final(ledger, &publication_owner);
        drop(launched);
        ledger_bind_final(ledger, &slab);
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
        bind_pass_owners_final(ledger, &owners);
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
            declared_eq_tables,
        )
    };
    assert_eq!(observation.memory.start, interval_entry);
    assert_eq!(observation.memory.return_to_entry, interval_entry);
    assert_eq!(
        declared_eq_tables,
        expected_declared_eq_regions(folding_steps, start_round),
        "Task 8 window arm declared an unexpected number of resident Eq regions"
    );
    observation.allocations = allocations;
    Ok(observation)
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
) -> CudaResult<(
    ScheduledPreparedObservation,
    Vec<(SourceId, usize)>,
    ContinuationPublishedShape,
    Task8AdoptionEvidence,
)> {
    let interval_entry = context.get_device_memory_usage();
    let observer = context.observe_device_memory_high_water();
    let (mut observation, source_columns, shape, adoption, allocations, declared_eq_tables) = {
        let mut allocations = Vec::new();
        let (claim_point, point_staging) = upload(context, point_host)?;
        let claim_symbol_staging = write_claim_point_symbol(context, point_host)?;
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
        let owners = open_pass_owners(
            ledger,
            TASK8_LEGACY_ARM,
            pass_addresses(&claim_point, point_host.len(), &eq_low, &partials),
        );
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
            &owners,
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
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )?;
        record_eq_build(ledger, &owners, folding_steps, start_round);
        let pre_sizes = make_eq_sizes(folding_steps - start_round - 3);
        let pre_eq =
            schedule_read_all_eq(pre_sizes, &eq_low, readback_scratch, callbacks, context)?;
        let declared_eq_tables = record_eq_readback(ledger, &owners);
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
        ledger_note(
            ledger,
            &owners.eq_low,
            0,
            active_eq_low_table(folding_steps - start_round - 3),
            Task8QueuedUse::Read,
        );
        if let Some(prior_owner) = prior_owner.as_ref() {
            // The segmented VM takes the published level here, so this hand-off
            // is the last use the arm itself names.
            ledger_note(
                ledger,
                prior_owner,
                0,
                prior_owner.elems,
                Task8QueuedUse::Read,
            );
            ledger_bind_final(ledger, prior_owner);
        }
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
        let slab = ledger_open(
            ledger,
            TASK8_LEGACY_ARM,
            "challenge_slab",
            rounds.challenge_slab(),
        );
        let input_live_before = rounds.expected_input_is_live();
        let first_deltas = rounds.first_deltas().to_vec();
        let first_reads_only_published = rounds.first_reads_only_published();
        let external_host: Vec<_> = (0..32).map(|i| deterministic_e4(0x100 + i)).collect();
        let (external, external_staging) = upload(context, &external_host)?;
        let (lookup_mul, lookup_mul_staging) = upload(context, &[deterministic_e4(0x201)])?;
        let (lookup_add, lookup_add_staging) = upload(context, &[deterministic_e4(0x202)])?;
        let (batching, batching_staging) = upload(context, &[deterministic_e4(0x203)])?;
        let challenge_owners = open_challenge_owners(
            ledger,
            TASK8_LEGACY_ARM,
            &external,
            &lookup_mul,
            &lookup_add,
            &batching,
        );
        rounds.schedule_bank_fill(
            external.as_ptr(),
            lookup_mul.as_ptr(),
            lookup_add.as_ptr(),
            batching.as_ptr(),
            context,
        )?;
        record_bank_fill(
            ledger,
            &slab,
            &challenge_owners.external,
            &challenge_owners.lookup_multiplicative,
            &challenge_owners.lookup_additive,
            &challenge_owners.claim_batching,
        );
        let mut transcript = transcript_buffers(context)?;
        allocations.append(&mut transcript.allocations);
        let transcript_owners = open_transcript_owners(ledger, TASK8_LEGACY_ARM, &transcript);
        let mut publication_owner = None;
        let mut raw_publication = None;
        for local_round in 0..3 {
            let round = start_round + local_round;
            let acc_size = 1usize << (folding_steps - round - 1);
            let before_round = context.get_device_memory_usage();
            rounds.schedule_round(round as u32, acc_size as u32, context)?;
            record_fold_weights(ledger, &owners, round);
            ledger_note(
                ledger,
                &owners.partials,
                0,
                warp_partial_count(acc_size),
                Task8QueuedUse::Write,
            );
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
                let owner = ledger_open(
                    ledger,
                    TASK8_LEGACY_ARM,
                    "publication",
                    rounds.live_publication(),
                );
                ledger_note(ledger, &owner, 0, owner.elems, Task8QueuedUse::Write);
                raw_publication = Some(schedule_read_device_chunked(
                    rounds.live_publication(),
                    readback_scratch,
                    callbacks,
                    context,
                )?);
                ledger_note(ledger, &owner, 0, owner.elems, Task8QueuedUse::Read);
                publication_owner = Some(owner);
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
            ledger_note(
                ledger,
                &owners.partials,
                0,
                warp_partial_count(acc_size),
                Task8QueuedUse::Read,
            );
            ledger_note(ledger, &owners.claim_point, round, 1, Task8QueuedUse::Read);
            record_transcript_finalize(
                ledger,
                &transcript_owners,
                4 * local_round..4 * local_round + 4,
                local_round..local_round + 1,
            );
            ledger_note_active_eq_slot(
                ledger,
                &owners.eq_low,
                &owners.eq_high,
                active_eq_slot_base,
                active_eq_size_before_fold,
            );
        }
        let mut post_sizes = pre_sizes;
        record_active_eq_slot_fold(&mut post_sizes);
        let source_columns = rounds.source_columns().to_vec();
        let shape = rounds.publication_shape();
        assert_eq!(shape.depth, start_round as u8);
        let publication = raw_publication.expect("Task 8 legacy round did not publish");
        let coefficients = schedule_read_device_chunked(
            &transcript.coefficients,
            readback_scratch,
            callbacks,
            context,
        )?;
        let challenges = schedule_read_device_chunked(
            &transcript.challenges,
            readback_scratch,
            callbacks,
            context,
        )?;
        let seed =
            schedule_read_device_chunked(&transcript.seed, readback_scratch, callbacks, context)?;
        let claim =
            schedule_read_device_chunked(&transcript.claim, readback_scratch, callbacks, context)?;
        let eq_prefactor = schedule_read_device_chunked(
            &transcript.prefactor,
            readback_scratch,
            callbacks,
            context,
        )?;
        record_transcript_readbacks(ledger, &transcript_owners);
        let post_eq =
            schedule_read_all_eq(post_sizes, &eq_low, readback_scratch, callbacks, context)?;
        assert_eq!(
            record_eq_readback(ledger, &owners),
            0,
            "Task 8 legacy arm left Eq bytes uncovered after the first readback"
        );
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
        ledger_bind_final(
            ledger,
            publication_owner
                .as_ref()
                .expect("Task 8 legacy round did not publish"),
        );
        ledger_bind_final(ledger, &slab);
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
        bind_pass_owners_final(ledger, &owners);
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
            declared_eq_tables,
        )
    };
    assert_eq!(observation.memory.start, interval_entry);
    assert_eq!(observation.memory.return_to_entry, interval_entry);
    assert_eq!(
        declared_eq_tables,
        expected_declared_eq_regions(folding_steps, start_round),
        "Task 8 legacy arm declared an unexpected number of resident Eq regions"
    );
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
    window_program: &MainContinuationWindowProgram,
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
        let claim_symbol_staging = write_claim_point_symbol(context, point_host)?;
        let mut eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?;
        let mut partials = context.alloc(
            window_partials_len(1usize << folding_steps),
            AllocationPlacement::BestFit,
        )?;
        let mut probe_ledger = Task8OwnerGenerationLedger::default();
        let probe_owners = open_pass_owners(
            &mut probe_ledger,
            TASK8_PROBE_ARM,
            pass_addresses(&claim_point, point_host.len(), &eq_low, &partials),
        );
        let (prior, prior_owner) = build_prior_level(
            storage,
            window_program,
            folding_steps,
            3,
            claim_point.as_ptr(),
            &mut eq_low,
            &mut partials,
            context,
            &mut probe_ledger,
            &probe_owners,
        )?;
        assert!(
            prior.is_none() && prior_owner.is_none(),
            "round-3 capacity probe must not retain a prior"
        );
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
        rounds.schedule_bank_fill(
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
            rounds.schedule_round(round as u32, acc_size as u32, context)?;
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

    use super::{
        allocation_group_record, bind_pass_owners_final, build_corpus_census,
        expected_declared_eq_regions, ledger_bind_final, ledger_open_raw, open_pass_owners,
        record_eq_build, record_eq_readback, record_fold_weights, record_window_launch,
        signed_snapshot_delta, validate_owner_generation_ledger, validate_single_owner_topology,
        Task8AllocationRecord, Task8GenerationToken, Task8LedgerEntry, Task8LedgerError,
        Task8LedgerOwner, Task8OwnerGenerationLedger, Task8PassAddresses, Task8PassOwners,
        Task8QueuedUse, Task8TopologyError, MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
        TASK8_LEGACY_ARM, TASK8_SHARED_DEVICE_SYMBOLS, TASK8_WINDOW_ARM,
    };

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

    const TASK8_TEST_FOLDING_STEPS: usize = 11;
    const TASK8_TEST_START_ROUND: usize = 3;
    const TASK8_TEST_ROW_TILES: usize = 4;
    const TASK8_TEST_PUBLICATION_ELEMS: usize = 8;
    const TASK8_TEST_ELEM_BYTES: usize = 16;
    const TASK8_TEST_ARM_RECORDS: u64 = 15;

    fn test_pass_addresses() -> Task8PassAddresses {
        Task8PassAddresses {
            claim_point: 0x10_0000,
            point_len: TASK8_TEST_FOLDING_STEPS + 1,
            claim_point_symbol: 0x20_0000,
            eq_low: 0x30_0000,
            eq_high: 0x40_0000,
            partials: 0x50_0000,
            partials_len: MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * (TASK8_TEST_ROW_TILES + 1),
        }
    }

    /// Replays one arm's continuation pass through the same recorders both real
    /// arms call, without binding `Final`.
    fn replay_continuation_arm(
        ledger: &mut Task8OwnerGenerationLedger,
        arm: &'static str,
    ) -> (Task8PassOwners, Task8LedgerOwner) {
        let owners = open_pass_owners(ledger, arm, test_pass_addresses());
        record_eq_build(
            ledger,
            &owners,
            TASK8_TEST_FOLDING_STEPS,
            TASK8_TEST_START_ROUND,
        );
        record_fold_weights(ledger, &owners, TASK8_TEST_START_ROUND);
        let publication = ledger_open_raw(
            ledger,
            arm,
            "publication",
            0x60_0000,
            TASK8_TEST_ELEM_BYTES,
            TASK8_TEST_PUBLICATION_ELEMS,
        );
        record_window_launch(
            ledger,
            &owners,
            TASK8_TEST_FOLDING_STEPS,
            TASK8_TEST_START_ROUND,
            None,
            TASK8_TEST_ROW_TILES,
            &publication,
        );
        assert_eq!(
            record_eq_readback(ledger, &owners),
            expected_declared_eq_regions(TASK8_TEST_FOLDING_STEPS, TASK8_TEST_START_ROUND)
        );
        (owners, publication)
    }

    fn finish_continuation_arm(
        ledger: &mut Task8OwnerGenerationLedger,
        owners: &Task8PassOwners,
        publication: &Task8LedgerOwner,
    ) {
        ledger_bind_final(ledger, publication);
        bind_pass_owners_final(ledger, owners);
    }

    fn symbol_read(
        ledger: &mut Task8OwnerGenerationLedger,
        owners: &Task8PassOwners,
    ) -> Result<u64, Task8LedgerError> {
        ledger.enqueue(
            owners.claim_point_symbol.token,
            owners.claim_point_symbol.base,
            TASK8_TEST_START_ROUND * TASK8_TEST_ELEM_BYTES,
            Task8QueuedUse::Read,
        )
    }

    #[test]
    fn cpu_main_continuation_owner_generation_admits_second_arm_in_both_orders() {
        for (first_arm, second_arm) in [
            (TASK8_WINDOW_ARM, TASK8_LEGACY_ARM),
            (TASK8_LEGACY_ARM, TASK8_WINDOW_ARM),
        ] {
            let mut ledger = Task8OwnerGenerationLedger::default();
            let (first, first_publication) = replay_continuation_arm(&mut ledger, first_arm);
            assert_eq!(ledger.next_sequence, TASK8_TEST_ARM_RECORDS);
            finish_continuation_arm(&mut ledger, &first, &first_publication);
            let first_symbol = ledger.generation(first.claim_point_symbol.token).clone();
            assert_eq!(first_symbol.generation, 2);
            assert_eq!(first_symbol.final_sequence, Some(6));
            assert_eq!(
                first_symbol.records[0].entry,
                Task8LedgerEntry::Enqueued(Task8QueuedUse::Write)
            );
            assert_eq!(first_symbol.records[0].sequence, 1);
            assert!(first_symbol.fully_initialized());

            let (second, second_publication) = replay_continuation_arm(&mut ledger, second_arm);
            let second_symbol = ledger.generation(second.claim_point_symbol.token).clone();
            assert_eq!(second_symbol.generation, 8);
            assert_eq!(second_symbol.owner, first_symbol.owner);
            assert_eq!(
                second_symbol.records[0].sequence,
                TASK8_TEST_ARM_RECORDS + 1
            );
            assert_eq!(
                ledger
                    .generation(first.claim_point_symbol.token)
                    .superseded_by,
                Some(second_symbol.generation)
            );
            assert_eq!(
                symbol_read(&mut ledger, &second),
                Ok(2 * TASK8_TEST_ARM_RECORDS)
            );
            finish_continuation_arm(&mut ledger, &second, &second_publication);

            assert_eq!(ledger.next_sequence, 2 * TASK8_TEST_ARM_RECORDS + 1);
            assert_eq!(ledger.generations.len(), 12);
            assert_eq!(
                validate_owner_generation_ledger(
                    &ledger,
                    first_arm,
                    second_arm,
                    &TASK8_SHARED_DEVICE_SYMBOLS
                ),
                TASK8_SHARED_DEVICE_SYMBOLS.len()
            );
        }
    }

    #[test]
    fn cpu_main_continuation_owner_generation_rejects_retired_arm_uses_in_both_orders() {
        for (first_arm, second_arm) in [
            (TASK8_WINDOW_ARM, TASK8_LEGACY_ARM),
            (TASK8_LEGACY_ARM, TASK8_WINDOW_ARM),
        ] {
            let mut ledger = Task8OwnerGenerationLedger::default();
            let (first, first_publication) = replay_continuation_arm(&mut ledger, first_arm);
            assert_eq!(symbol_read(&mut ledger, &first), Ok(TASK8_TEST_ARM_RECORDS));
            finish_continuation_arm(&mut ledger, &first, &first_publication);
            let (second, second_publication) = replay_continuation_arm(&mut ledger, second_arm);

            assert_eq!(
                symbol_read(&mut ledger, &first),
                Err(Task8LedgerError::UseAfterFinal)
            );
            assert_eq!(
                ledger.enqueue(
                    first.eq_high.token,
                    first.eq_high.base,
                    TASK8_TEST_ELEM_BYTES,
                    Task8QueuedUse::Read
                ),
                Err(Task8LedgerError::UseAfterFinal)
            );
            assert_eq!(
                ledger.declare_initialized(
                    first.eq_high.token,
                    first.eq_high.base,
                    TASK8_TEST_ELEM_BYTES,
                    "retired generation"
                ),
                Err(Task8LedgerError::UseAfterFinal)
            );
            assert!(symbol_read(&mut ledger, &second).is_ok());
            finish_continuation_arm(&mut ledger, &second, &second_publication);
            assert_eq!(
                validate_owner_generation_ledger(
                    &ledger,
                    first_arm,
                    second_arm,
                    &TASK8_SHARED_DEVICE_SYMBOLS
                ),
                TASK8_SHARED_DEVICE_SYMBOLS.len()
            );
        }
    }

    #[test]
    fn cpu_main_continuation_owner_generation_rejects_missing_reordered_and_partial_coverage() {
        const BASE: usize = 0x70_0000;
        let mut ledger = Task8OwnerGenerationLedger::default();
        let owner = ledger_open_raw(
            &mut ledger,
            TASK8_WINDOW_ARM,
            "eq",
            BASE,
            TASK8_TEST_ELEM_BYTES,
            4,
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 64, Task8QueuedUse::Read),
            Err(Task8LedgerError::UseBeforeInitialization)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 32, Task8QueuedUse::Write),
            Ok(0)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 64, Task8QueuedUse::Read),
            Err(Task8LedgerError::UseBeforeInitialization)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE + 32, 32, Task8QueuedUse::Mutation),
            Err(Task8LedgerError::UseBeforeInitialization)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 32, Task8QueuedUse::Read),
            Ok(1)
        );
        assert_eq!(
            ledger.declare_initialized(owner.token, BASE, 32, "already covered"),
            Err(Task8LedgerError::DeclarationOverlapsCoverage)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE + 32, 32, Task8QueuedUse::Write),
            Ok(2)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 64, Task8QueuedUse::Read),
            Ok(3)
        );
        assert!(ledger.generation(owner.token).fully_initialized());
        assert_eq!(
            ledger.generation(owner.token).initialized,
            vec![BASE..BASE + 64]
        );
        assert_eq!(ledger.bind_final(owner.token), Ok(3));

        let mut partial = Task8OwnerGenerationLedger::default();
        let half = ledger_open_raw(
            &mut partial,
            TASK8_WINDOW_ARM,
            "eq",
            BASE,
            TASK8_TEST_ELEM_BYTES,
            4,
        );
        partial
            .enqueue(half.token, BASE, 32, Task8QueuedUse::Write)
            .unwrap();
        partial.bind_final(half.token).unwrap();
        let successor = partial.open(TASK8_LEGACY_ARM, "eq", BASE, 64).unwrap();
        assert!(partial.generation(successor).initialized.is_empty());
        assert_eq!(
            partial.enqueue(successor, BASE, 32, Task8QueuedUse::Read),
            Err(Task8LedgerError::UseBeforeInitialization)
        );
    }

    #[test]
    fn cpu_main_continuation_owner_generation_rejects_post_final_and_out_of_range_uses() {
        const BASE: usize = 0x80_0000;
        let mut ledger = Task8OwnerGenerationLedger::default();
        let owner = ledger_open_raw(
            &mut ledger,
            TASK8_WINDOW_ARM,
            "publication",
            BASE,
            TASK8_TEST_ELEM_BYTES,
            4,
        );
        assert_eq!(
            ledger.bind_final(owner.token),
            Err(Task8LedgerError::FinalWithoutUse)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 64, Task8QueuedUse::Write),
            Ok(0)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 65, Task8QueuedUse::Read),
            Err(Task8LedgerError::OutOfCoverage)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE - 16, 16, Task8QueuedUse::Read),
            Err(Task8LedgerError::OutOfCoverage)
        );
        assert_eq!(
            ledger.declare_initialized(owner.token, BASE, 0, "empty"),
            Err(Task8LedgerError::OutOfCoverage)
        );
        assert_eq!(ledger.bind_final(owner.token), Ok(0));
        assert_eq!(
            ledger.bind_final(owner.token),
            Err(Task8LedgerError::FinalAlreadyBound)
        );
        assert_eq!(
            ledger.enqueue(owner.token, BASE, 64, Task8QueuedUse::Read),
            Err(Task8LedgerError::UseAfterFinal)
        );
        assert_eq!(ledger.next_sequence, 1);
    }

    #[test]
    fn cpu_main_continuation_owner_generation_binds_repeated_addresses_by_token() {
        const BASE: usize = 0x90_0000;
        let mut ledger = Task8OwnerGenerationLedger::default();
        let first = ledger_open_raw(
            &mut ledger,
            TASK8_WINDOW_ARM,
            "publication",
            BASE,
            TASK8_TEST_ELEM_BYTES,
            2,
        );
        ledger
            .enqueue(first.token, BASE, 32, Task8QueuedUse::Write)
            .unwrap();
        assert_eq!(
            ledger.open(TASK8_LEGACY_ARM, "publication", BASE, 32),
            Err(Task8LedgerError::ReuseWithoutFinal)
        );
        ledger.bind_final(first.token).unwrap();
        let second = ledger_open_raw(
            &mut ledger,
            TASK8_LEGACY_ARM,
            "publication",
            BASE,
            TASK8_TEST_ELEM_BYTES,
            2,
        );
        assert_ne!(first.token.generation, second.token.generation);
        assert_eq!(ledger.live_generation(BASE), Ok(Some(second.token)));
        assert_eq!(
            ledger.admit_reuse(
                TASK8_WINDOW_ARM,
                "publication",
                first.token,
                BASE..BASE + 32
            ),
            Err(Task8LedgerError::StaleToken)
        );
        assert_eq!(
            ledger.enqueue(first.token, BASE, 32, Task8QueuedUse::Read),
            Err(Task8LedgerError::UseAfterFinal)
        );
        ledger
            .enqueue(second.token, BASE, 32, Task8QueuedUse::Write)
            .unwrap();
        assert_eq!(
            ledger.enqueue(second.token, BASE, 32, Task8QueuedUse::Read),
            Ok(2)
        );
        assert_eq!(ledger.generations.len(), 2);
        assert_eq!(ledger.generation(first.token).records.len(), 1);
        assert_eq!(ledger.generation(second.token).records.len(), 2);
        let forged = Task8GenerationToken {
            slot: second.token.slot,
            owner: BASE,
            generation: second.token.generation + 1,
        };
        assert_eq!(
            ledger.enqueue(forged, BASE, 32, Task8QueuedUse::Read),
            Err(Task8LedgerError::StaleToken)
        );
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
            window_program,
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
            let window = run_window_arm(
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
                            expected_arm_owner_labels(start_round),
                            "Task 8 {arm} arm opened an unexpected owner set"
                        );
                        assert_eq!(
                            owner_ledger.label_generations(arm, "prior_publication"),
                            start_round / 3 - 1,
                            "Task 8 {arm} arm published an unexpected number of prior levels"
                        );
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
            let plan_passes = usize::from(plan);
            assert_eq!(state.ledger_coordinates, state.topology_coordinates);
            assert_eq!(
                state.ledger_shared_symbol_transitions,
                TASK8_SHARED_DEVICE_SYMBOLS.len() * state.topology_coordinates
            );
            assert_eq!(
                state.ledger_owner_generations,
                2 * (expected_arm_owner_labels(3).len() * state.topology_coordinates
                    + state.layers * plan_passes * (plan_passes - 1) / 2)
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
