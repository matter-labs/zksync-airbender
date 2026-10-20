import Slop.Trace.Paths

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

theorem zip_fst_sublist {S T : Type} (left : List S) (right : List T) :
    List.Sublist ((left.zip right).map Prod.fst) left := by
  induction left generalizing right with
  | nil => simp
  | cons head tail ih =>
    cases right with
    | nil => simp
    | cons _ rest =>
      simpa only [List.zip_cons_cons, List.map_cons] using (ih rest).cons_cons head

theorem state_clocks_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (constraints : ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    (trace.rows.map fun row => (decodeTimestamp row.assignment row.columns.initialTime).value).Nodup := by
  obtain ⟨path, head, last, permutation, clockUnique⟩ := state_path_checks hp inverse constraints states initial aligned
  let rank := fun state : PCState.State p => (timeOfPair state.timestamp).value
  have earlierRanks : (((path.zip path.tail).map Prod.fst).map rank).Nodup :=
    List.Nodup.sublist ((zip_fst_sublist path path.tail).map rank) clockUnique
  have ranks := permutation.map (fun edge => rank edge.1)
  have unique := ranks.nodup_iff.mp (by
    simpa only [List.map_map, Function.comp_def] using earlierRanks)
  simpa only [List.map_map, Function.comp_def, rank, Row.start, timeOfPair,
    rawPair, decodeTimestamp] using unique

theorem row_clocks_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    (trace.rows.map fun row => (decodeTimestamp row.assignment row.columns.initialTime).value).Nodup :=
  state_clocks_unique hp inverse accepted.constraints accepted.states boundary.initial boundary.aligned

private def slots (time : Nat) : List Nat := [time, time + 1, time + 2]

theorem slots_unique {times : List Nat} (unique : times.Nodup)
    (aligned : ∀ time ∈ times, time % 4 = 0) : (times.flatMap slots).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro time _
    simp [slots]
  · apply List.Pairwise.imp_of_mem _ unique
    intro first last firstMember lastMember different left leftMember right rightMember equal
    have firstAligned := aligned first firstMember
    have lastAligned := aligned last lastMember
    simp [slots] at leftMember rightMember
    rcases leftMember with rfl | rfl | rfl <;>
      rcases rightMember with rfl | rfl | rfl <;> omega

private theorem row_slots [Fact p.Prime] [ClockLaws Kind p] (row : Row p Kind) :
    row.ports.toList.map (fun port =>
      (decodeTimestamp row.assignment row.columns.initialTime).value + port.clock.offset) =
      slots (decodeTimestamp row.assignment row.columns.initialTime).value := by
  have offsets := ClockLaws.offsets row
  have mapped := congrArg (List.map ((decodeTimestamp row.assignment row.columns.initialTime).value + ·)) offsets
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    Nat.add_zero, slots] using mapped

/-- Every actual native memory-access write time is unique across all selected
    rows, including readonly refreshes. Imported offsets are 0/1/2. -/
theorem access_times_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) : trace.accessTimes.Nodup := by
  let times := trace.rows.map fun row =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have unique := row_clocks_unique hp inverse accepted boundary
  have aligned : ∀ time ∈ times, time % 4 = 0 := by
    intro time member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    have inputs := clock_inputs hp inverse accepted boundary row rowMember
    simpa [Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using inputs.aligned
  have concrete : trace.accessTimes = times.flatMap slots := by
    simp only [Data.accessTimes, times, List.flatMap_map]
    apply congrArg (fun f : Row p Kind → List Nat => trace.rows.flatMap f)
    funext row
    exact row_slots row
  rw [concrete]
  exact slots_unique unique aligned

end Airbender.Trace.Proofs
