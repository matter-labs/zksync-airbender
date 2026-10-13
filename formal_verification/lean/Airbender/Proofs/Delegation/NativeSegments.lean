import Airbender.Review.Helpers.Delegation.NativeWindows
import Airbender.Proofs.Delegation.Values
import Airbender.Proofs.Delegation.SailHistory
import Airbender.Proofs.Trace.TransferBoundary

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

abbrev rowWriteTime (row : Row p) : Nat := row.writeTime

abbrev windowRows (data : MemoryData p) (lower upper : Nat) : List (Row p) :=
  data.windowRows lower upper

def native_window_boundary_inputs {data : MemoryData p} {before atStart : State} {cells : List Cell}
    (inputs : MemoryInputs data before cells) {lower upper : Nat} {start finish : List (MemoryToken p)}
    (boundary : Transfer.NativeInputs
      (transferData ⟨data.setup, windowRows data lower upper, start, finish⟩) atStart cells) :
    BoundaryMemoryInputs ⟨data.setup, windowRows data lower upper, start, finish⟩ atStart cells :=
  ⟨boundary_image boundary, boundary.distinct, boundary.clocks,
    fun row member => inputs.clockRoom row (List.mem_of_mem_filter member)⟩

def native_window_boundary_inputs_at_boundary {data : MemoryData p} {before atStart : State}
    {cells : List Cell} (inputs : BoundaryInputs data before cells) {lower upper : Nat}
    {start finish : List (MemoryToken p)}
    (boundary : Transfer.NativeInputs
      (transferData ⟨data.setup, windowRows data lower upper, start, finish⟩) atStart cells) :
    BoundaryMemoryInputs ⟨data.setup, windowRows data lower upper, start, finish⟩ atStart cells :=
  ⟨boundary_image boundary, boundary.distinct, boundary.clocks,
    fun row member => inputs.clockRoom row (List.mem_of_mem_filter member)⟩

theorem row_write_time (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    (timeOfPair (row.writeToken port).time).value = rowWriteTime row := by
  simp only [Row.writeToken, port_offset row member, rowWriteTime]
  rfl

theorem native_window_steps (data : MemoryData p) (lower upper : Nat) :
    (windowRows data lower upper).flatMap Row.memorySteps =
      Transfer.windowSteps (transferData data) lower upper := by
  have rowFilter (row : Row p) :
      row.memorySteps.filter (fun edge =>
        decide ((timeOfPair edge.2.time).value ≤ upper) &&
          !decide ((timeOfPair edge.2.time).value ≤ lower)) =
      if lower < rowWriteTime row ∧ rowWriteTime row ≤ upper then row.memorySteps else [] := by
    by_cases inside : lower < rowWriteTime row ∧ rowWriteTime row ≤ upper
    · rw [if_pos inside]
      apply List.filter_eq_self.mpr
      intro edge member
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
      rw [row_write_time row (by simpa using present)]
      simp [Nat.not_le.mpr inside.1, inside.2]
    · rw [if_neg inside]
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
      rw [row_write_time row (by simpa using present)]
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Nat.not_le, decide_eq_true_eq, and_comm] using inside
  simp only [windowRows, MemoryData.windowRows, Transfer.windowSteps, Transfer.beforeSteps, Transfer.afterSteps,
    transferData, MemoryData.steps, List.filter_filter, List.filter_flatMap]
  induction data.rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    rw [rowFilter]
    by_cases inside : lower < rowWriteTime row ∧ rowWriteTime row ≤ upper
    · simp only [decide_eq_true inside, if_true, if_pos inside, List.flatMap_cons, ih]
    · simp only [decide_eq_false inside, Bool.false_eq_true, if_false, if_neg inside,
        List.nil_append, ih]

theorem native_prefix_steps (data : MemoryData p) (cutoff : Nat) :
    (data.prefixRows cutoff).flatMap Row.memorySteps =
      Transfer.beforeSteps (transferData data) cutoff := by
  have rowFilter (row : Row p) :
      row.memorySteps.filter (fun edge => decide ((timeOfPair edge.2.time).value ≤ cutoff)) =
      if row.writeTime ≤ cutoff then row.memorySteps else [] := by
    by_cases inside : row.writeTime ≤ cutoff
    · rw [if_pos inside]
      apply List.filter_eq_self.mpr
      intro edge member
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
      rw [row_write_time row (by simpa using present)]
      exact decide_eq_true inside
    · rw [if_neg inside]
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
      rw [row_write_time row (by simpa using present)]
      simpa only [decide_eq_true_eq] using inside
  simp only [MemoryData.prefixRows, Transfer.beforeSteps, transferData, MemoryData.steps,
    List.filter_flatMap]
  induction data.rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    rw [rowFilter]
    by_cases inside : row.writeTime ≤ cutoff
    · simp only [decide_eq_true inside, if_true, if_pos inside, List.flatMap_cons, ih]
    · simp only [decide_eq_false inside, Bool.false_eq_true, if_false, if_neg inside,
        List.nil_append, ih]

def NativeWindow [Fact p.Prime] (data : MemoryData p) (before : State) (cells : List Cell)
    (lower upper : Nat) : Prop :=
    ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
      (atStart atFinish : State),
      Transfer.Facts ⟨data.initial, start, Transfer.beforeSteps (transferData data) lower⟩ ∧
      MemoryAccepted ⟨data.setup, windowRows data lower upper, start, finish⟩ ∧
      earlierEvents.Perm ((Transfer.beforeSteps (transferData data) lower).map transferEvent) ∧
      spanEvents.Perm (((windowRows data lower upper).flatMap Row.memorySteps).map transferEvent) ∧
      SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
      Transfer.NativeInputs (transferData ⟨data.setup, windowRows data lower upper, start, finish⟩)
        atStart cells ∧
      Transfer.NativeInputs ⟨finish, data.terminal,
        Transfer.afterSteps ⟨start, data.terminal, Transfer.afterSteps (transferData data) lower⟩ upper⟩
        atFinish cells

theorem native_span_window_at_boundary [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    (rules : WriteBoundsFromReads data) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (lower upper : Nat) : NativeWindow data before cells lower upper := by
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstFacts, facts,
      firstPerm, spanPerm, firstHistory, spanHistory, startInputs, finishInputs⟩ :=
    Transfer.split_native_sail_window_at_boundary (transfer_facts hp accepted inputs)
      inputs.toNativeInputs
      (transfer_write_rules rules)
      (fun edge member => (memory_clocks (by omega) accepted inputs edge member).2) aligned
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

theorem native_span_window [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (rules : WriteBoundsFromReads data) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (lower upper : Nat) : NativeWindow data before cells lower upper :=
  native_span_window_at_boundary hp accepted inputs.toBoundaryInputs rules aligned lower upper

end Airbender.Delegation.Proofs
