module
public import Proven.Delegation.NativeSegments
public import Proven.Delegation.RVCallHistory
public import Proven.Delegation.RVCallLink
public import Proven.Trace.RVTransferWindow

@[expose] public section

/-! RV twins of `NativeSegments.lean` and `HashWindowTransport.lean`: a delegation pool's RV history cut at two
    native-clock times, the cut states' boundary inputs, and the uniqueness of a span's final state: two RV states
    that execute the same native accesses from one start and agree with its terminal tokens are `RV.Same`. RAM cells
    are RAM at any address, the shadow RAM below `ROM_END` included. -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_boundary_image {data : Transfer.Data p} {before : RV.State} {cells : List Cell}
    (inputs : Transfer.RVNativeInputs data before cells) : RVBoundaryImage data.initial before cells := by
  refine ⟨inputs.addresses, ?_⟩
  intro token member
  obtain ⟨cell, present, code, read⟩ := inputs.reads token member
  refine ⟨cell, present, token.word.toBitVec, code, by simpa only [memoryWord, MemoryToken.word] using read, ?_⟩
  exact (word_of_toBitVec (inputs.words token member)).symm

theorem rv_native_window_boundary_inputs_at_boundary {data : MemoryData p} {before atStart : RV.State}
    {cells : List Cell} (inputs : RVBoundaryInputs data before cells) {lower upper : Nat}
    {start finish : List (MemoryToken p)}
    (boundary : Transfer.RVNativeInputs
      (transferData ⟨data.setup, windowRows data lower upper, start, finish⟩) atStart cells) :
    RVBoundaryMemoryInputs ⟨data.setup, windowRows data lower upper, start, finish⟩ atStart cells :=
  ⟨rv_boundary_image boundary, boundary.distinct, boundary.clocks,
    fun row member => inputs.toSeed.clockRoom row (List.mem_of_mem_filter member),
    fun row member => inputs.toSeed.invocationHigh row (List.mem_of_mem_filter member)⟩

/-- RV sibling of `NativeWindow`. -/
def RVNativeWindow [Fact p.Prime] (data : MemoryData p) (before : RV.State) (cells : List Cell)
    (lower upper : Nat) : Prop :=
    ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
      (atStart atFinish : RV.State),
      Transfer.Facts ⟨data.initial, start, Transfer.beforeSteps (transferData data) lower⟩ ∧
      MemoryAccepted ⟨data.setup, windowRows data lower upper, start, finish⟩ ∧
      earlierEvents.Perm ((Transfer.beforeSteps (transferData data) lower).map transferEvent) ∧
      spanEvents.Perm (((windowRows data lower upper).flatMap Row.memorySteps).map transferEvent) ∧
      RVHistory cells earlierEvents before atStart ∧ RVHistory cells spanEvents atStart atFinish ∧
      Transfer.RVNativeInputs (transferData ⟨data.setup, windowRows data lower upper, start, finish⟩)
        atStart cells ∧
      Transfer.RVNativeInputs ⟨finish, data.terminal,
        Transfer.afterSteps ⟨start, data.terminal, Transfer.afterSteps (transferData data) lower⟩ upper⟩
        atFinish cells

theorem rv_native_span_window_at_boundary [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : RV.State} {cells : List Cell} (inputs : RVBoundaryInputs data before cells)
    (rules : WriteBoundsFromReads data) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (lower upper : Nat) : RVNativeWindow data before cells lower upper := by
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstFacts, facts,
      firstPerm, spanPerm, firstHistory, spanHistory, startInputs, finishInputs⟩ :=
    Transfer.rv_split_native_window_at_boundary (SeedProofs.transfer_facts hp accepted inputs.toSeed)
      ⟨inputs.transfer, inputs.toSeed.words, inputs.toSeed.clocks⟩
      (transfer_write_rules rules)
      (fun edge member => (SeedProofs.memory_clocks (by omega) accepted inputs.toSeed edge member).2) aligned
      (by
        intro edge present same
        obtain ⟨row, _, step⟩ := List.mem_flatMap.mp present
        obtain ⟨port, member, rfl⟩ := List.mem_map.mp step
        exact False.elim (port_not_zero row (by simpa using member) same)) lower upper
  rw [← native_window_steps] at facts spanPerm startInputs
  refine ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish,
    firstFacts, ⟨?_, facts.matching⟩, firstPerm, spanPerm, firstHistory, spanHistory, startInputs, finishInputs⟩
  intro row member
  exact accepted.constraints row (List.mem_of_mem_filter member)

theorem rv_empty_prefix_state {data : MemoryData p} {lower : Nat}
    {cells : List Cell} {events : List MemoryAccess} {before after : RV.State}
    (empty : data.prefixRows lower = [])
    (permutation : events.Perm ((Trace.Proofs.Transfer.beforeSteps (transferData data) lower).map transferEvent))
    (history : RVHistory cells events before after) : after = before := by
  rw [← native_prefix_steps, empty] at permutation
  have emptyEvents : events = [] := by
    cases events with
    | nil => rfl
    | cons event rest =>
      have count := permutation.length_eq
      simp at count
  subst events
  cases history
  rfl

/-- Two RV states reached from one start by histories over the tracked cells, both agreeing with the terminal tokens
    (whose addresses are the tracked cells'), are `RV.Same`. -/
theorem rv_trace_mapping_same {data : MemoryData p} {initial first last : RV.State} {cells : List Cell}
    (source : RVTraceMapping data initial first cells) (target : RVTraceMapping data initial last cells)
    (addresses : (data.terminal.map MemoryToken.address).Perm (cells.map Cell.addressCode))
    (aligned : ∀ cell ∈ cells, cell.Aligned) : RV.Same first last := by
  obtain ⟨sourceEvents, _, sourceHistory⟩ := source.history
  obtain ⟨targetEvents, _, targetHistory⟩ := target.history
  have sourceFields := rv_history_fields sourceHistory
  have targetFields := rv_history_fields targetHistory
  have cellReads (cell : Cell) (cellAligned : cell.Aligned) : cell.readRV first = cell.readRV last := by
    by_cases tracked : cell ∈ cells
    · obtain ⟨token, present, code⟩ := List.mem_map.mp
        (addresses.mem_iff.mpr (List.mem_map.mpr ⟨cell, tracked, rfl⟩))
      obtain ⟨one, _, oneCode, oneRead⟩ := source.finalCells token present
      obtain ⟨two, _, twoCode, twoRead⟩ := target.finalCells token present
      have sameOne : one = cell := cell_address_injective (oneCode.trans code)
      have sameTwo : two = cell := cell_address_injective (twoCode.trans code)
      subst one two
      rw [oneRead, twoRead]
    · have untouched {events : List MemoryAccess} {origin target : RV.State}
          (history : RVHistory cells events origin target) : ∀ event ∈ events, event.2.1 ≠ cell.addressCode := by
        intro event present same
        obtain ⟨other, member, code⟩ := rv_history_address_member history present
        have equal : other = cell := cell_address_injective (code.trans same)
        exact tracked (equal ▸ member)
      have start : ∃ value, cell.readRV initial = some value := by
        cases cell with
        | register index => exact ⟨_, readRV_register index initial⟩
        | ram address => exact ⟨_, readRV_ram initial (readable_of_aligned cellAligned)⟩
      obtain ⟨value, read⟩ := start
      rw [rv_history_cell_frame sourceHistory aligned cell cellAligned (untouched sourceHistory) read,
        rv_history_cell_frame targetHistory aligned cell cellAligned (untouched targetHistory) read]
  refine ⟨sourceFields.1.trans targetFields.1.symm, ?_, sourceFields.2.1.trans targetFields.2.1.symm, ?_,
    sourceFields.2.2.trans targetFields.2.2.symm⟩
  · intro r
    have reads := cellReads (.register r) trivial
    rw [readRV_register, readRV_register] at reads
    exact Option.some.inj reads
  · apply mem_ext_of_words
    intro a alignedA
    have reads := cellReads (.ram a) alignedA
    rw [readRV_ram first (readable_of_aligned alignedA), readRV_ram last (readable_of_aligned alignedA)] at reads
    exact Option.some.inj reads

end Airbender.Delegation.Proofs
