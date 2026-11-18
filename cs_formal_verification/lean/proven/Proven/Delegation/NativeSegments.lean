module
public import Human.Helpers.Delegation.NativeWindows
public import Proven.Trace.TransferBoundary
public import Proven.Delegation.BoundaryInputs
public import Proven.Delegation.Memory

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

abbrev rowWriteTime (row : Row p) : Nat := row.writeTime

abbrev windowRows (data : MemoryData p) (lower upper : Nat) : List (Row p) :=
  data.windowRows lower upper

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
    · rw [ite_eq_left inside]
      apply List.filter_eq_self.mpr
      intro edge member
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
      rw [row_write_time row (by simpa using present)]
      simp [Nat.not_le.mpr inside.1, inside.2]
    · rw [ite_eq_right inside]
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
    · simp only [decide_eq_true inside, ite_true, ite_eq_left inside, List.flatMap_cons, ih]
    · simp only [decide_eq_false inside, Bool.false_eq_true, ite_false, ite_eq_right inside,
        List.nil_append, ih]

theorem native_prefix_steps (data : MemoryData p) (cutoff : Nat) :
    (data.prefixRows cutoff).flatMap Row.memorySteps =
      Transfer.beforeSteps (transferData data) cutoff := by
  have rowFilter (row : Row p) :
      row.memorySteps.filter (fun edge => decide ((timeOfPair edge.2.time).value ≤ cutoff)) =
      if row.writeTime ≤ cutoff then row.memorySteps else [] := by
    by_cases inside : row.writeTime ≤ cutoff
    · rw [ite_eq_left inside]
      apply List.filter_eq_self.mpr
      intro edge member
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp member
      rw [row_write_time row (by simpa using present)]
      exact decide_eq_true inside
    · rw [ite_eq_right inside]
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
    · simp only [decide_eq_true inside, ite_true, ite_eq_left inside, List.flatMap_cons, ih]
    · simp only [decide_eq_false inside, Bool.false_eq_true, ite_false, ite_eq_right inside,
        List.nil_append, ih]

end Airbender.Delegation.Proofs
