import Airbender.Proofs.Trace.ZeroRegister

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail

/-- The imported ports, retaining their native order and shifted access clocks. -/
def rowEvents (epoch : Nat) (row : Row p) : List MemoryAccess :=
  row.ports.toList.map fun port =>
    ((epoch + (port.event row.columns row.assignment).1,
      port.address.code row.assignment, port.readCode row.assignment,
      port.writeCode row.assignment) : MemoryAccess)

def rowClock (row : Row p) : Nat :=
  (decodeTimestamp row.assignment row.columns.initialTime).value

theorem native_events_projection [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    trace.nativeEvents = trace.rows.flatMap (rowEvents trace.memoryEpoch) := by
  simp only [Data.nativeEvents, Data.memorySteps, List.map_flatMap]
  apply List.flatMap_congr
  intro row member
  simp only [Row.memorySteps, List.map_map, Function.comp_def, rowEvents]
  apply List.map_congr_left
  intro port present
  have actual : port ∈ row.ports := by simpa using present
  have inputs := clock_inputs hp inverse accepted boundary row member
  have time := (write_time (by omega)
    (base := rawPair row.assignment row.columns.initialTime)
    inputs.initial inputs.aligned (port_offset row port actual)).2
  have canonical : (timeOfPair (writeToken row.columns row.assignment port).time).value =
      (port.event row.columns row.assignment).1 := time
  change (trace.memoryEpoch + (timeOfPair (writeToken row.columns row.assignment port).time).value,
    _, _, _) = (trace.memoryEpoch + (port.event row.columns row.assignment).1, _, _, _)
  rw [canonical]
  rfl

private theorem row_events_sorted (epoch : Nat) (row : Row p) :
    MemoryAccessList.isTimestampSorted (rowEvents epoch row).reverse := by
  cases row with
  | mk family w =>
    cases family <;>
      simp [rowEvents, Row.ports, MemoryPort.event,
        AddSub.importedConstraintsMemoryPorts, WordMemory.importedConstraintsMemoryPorts,
        MemoryAccessList.isTimestampSorted]

private theorem row_events_separated [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {first last : Row p} (firstMember : first ∈ trace.rows) (lastMember : last ∈ trace.rows)
    (ordered : rowClock last < rowClock first)
    {a b : MemoryAccess} (firstEvent : a ∈ (rowEvents trace.memoryEpoch first).reverse)
    (lastEvent : b ∈ (rowEvents trace.memoryEpoch last).reverse) : b.1 < a.1 := by
  obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp firstEvent)
  obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp lastEvent)
  have lo := port_offset first left (by simpa using leftMember)
  have ro := port_offset last right (by simpa using rightMember)
  have fa : rowClock first % 4 = 0 := by
    simpa [rowClock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using
      (clock_inputs hp inverse accepted boundary first firstMember).aligned
  have la : rowClock last % 4 = 0 := by
    simpa [rowClock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using
      (clock_inputs hp inverse accepted boundary last lastMember).aligned
  change trace.memoryEpoch + (rowClock last + right.clock.offset) <
    trace.memoryEpoch + (rowClock first + left.clock.offset)
  omega

/-- Strict clocks give an instruction ordering, and each instruction's three
    accesses stay together. Neither witness row order nor expected reads are used. -/
theorem native_row_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∃ rows : List (Row p), rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      MemoryAccessList.isTimestampSorted
        (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) ∧
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
  let rows := trace.rows.mergeSort (fun a b => decide (rowClock b ≤ rowClock a))
  have permutation : rows.Perm trace.rows := List.mergeSort_perm _ _
  have weak : rows.Pairwise (fun a b => rowClock b ≤ rowClock a) := by
    have sorted := List.pairwise_mergeSort
      (le := fun a b : Row p => decide (rowClock b ≤ rowClock a))
      (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) trace.rows
    simpa only [decide_eq_true_eq] using sorted
  have unique : (rows.map rowClock).Nodup :=
    (permutation.map rowClock).nodup_iff.mpr (row_clocks_unique hp inverse accepted boundary)
  have strict : rows.Pairwise (fun a b => rowClock b < rowClock a) :=
    (weak.and (List.pairwise_map.mp unique)).imp (by intro a b both; omega)
  refine ⟨rows, permutation, strict, ?_, ?_⟩
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro row _
      exact row_events_sorted _ row
    · apply List.Pairwise.imp_of_mem _ strict
      intro first last fm lm ordered a am b bm
      exact row_events_separated hp inverse accepted boundary
        (permutation.mem_iff.mp fm) (permutation.mem_iff.mp lm) ordered am bm
  · rw [native_events_projection hp inverse accepted boundary]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)

/-- The grouped instruction order is the complete native PC/timestamp path,
    including its public initial and terminal states. -/
theorem ordered_row_state_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {rows : List (Row p)} (permutation : rows.Perm trace.rows)
    (ordered : rows.Pairwise (fun a b => rowClock b < rowClock a)) :
    ∃ path, StatePath trace path ∧
      (path.zip path.tail).reverse = rows.map (fun row => (row.start, row.finish)) := by
  obtain ⟨path, head, last, edges, unique⟩ := native_state_path hp inverse accepted boundary
  let rank := fun state : PCState.State p => (timeOfPair state.timestamp).value
  have statesSorted := rank_ordered rank path (by
    intro edge member
    obtain ⟨row, present, equal⟩ := List.mem_map.mp (edges.mem_iff.mp member)
    subst edge
    have advance := (trace_clocks hp inverse accepted boundary row present).advances
    change (decodeTimestamp row.assignment row.columns.initialTime).value <
      (decodeTimestamp row.assignment row.columns.finalTime).value
    omega)
  have edgeRanks := statesSorted.sublist ((zip_fst_sublist path path.tail).map rank)
  have edgesSorted : (path.zip path.tail).Pairwise (fun a b => rank a.1 < rank b.1) := by
    apply List.pairwise_map.mp
    simpa only [List.map_map, Function.comp_def] using edgeRanks
  have reversed : (path.zip path.tail).reverse.Pairwise (fun a b => rank b.1 < rank a.1) :=
    List.pairwise_reverse.mpr edgesSorted
  have rowEdges : (rows.map fun row => (row.start, row.finish)).Pairwise
      (fun a b => rank b.1 < rank a.1) := List.pairwise_map.mpr ordered
  have mapped := permutation.map (fun row => (row.start, row.finish))
  exact ⟨path, ⟨head, last, edges, unique⟩,
    List.Perm.eq_of_pairwise' reversed rowEdges ((List.reverse_perm _).trans (edges.trans mapped.symm))⟩

/-- Split a native Sail history at an instruction boundary. Lists are stored
    backwards: the suffix executes before the prefix. -/
theorem sail_history_append {cells : List Cell} {new old : List MemoryAccess}
    {before after : State} :
    SailHistory cells (new ++ old) before after ↔
      ∃ middle, SailHistory cells old before middle ∧ SailHistory cells new middle after := by
  constructor
  · intro history
    induction new generalizing after with
    | nil => exact ⟨after, history, .nil after⟩
    | cons event rest ih =>
      cases history with
      | cons past cell member address read written =>
        obtain ⟨middle, oldHistory, newHistory⟩ := ih past
        exact ⟨middle, oldHistory, .cons newHistory cell member address read written⟩
  · rintro ⟨middle, oldHistory, newHistory⟩
    induction newHistory with
    | nil => exact oldHistory
    | cons past cell member address read written ih =>
      exact .cons (ih oldHistory) cell member address read written

/-- The first two native ports refresh clocks without changing Sail state.
    All three reads therefore come from the same instruction pre-state, even
    when their addresses alias. The third port supplies the actual update. -/
theorem sail_history_row_reads {cells : List Cell} {a b c : MemoryAccess}
    {before after : State} (history : SailHistory cells [c, b, a] before after)
    (firstReadonly : a.2.2.1 = a.2.2.2) (secondReadonly : b.2.2.1 = b.2.2.2) :
    ∃ left right destination : Cell,
      left ∈ cells ∧ right ∈ cells ∧ destination ∈ cells ∧
      left.addressCode = a.2.1 ∧ right.addressCode = b.2.1 ∧ destination.addressCode = c.2.1 ∧
      left.read before = .ok (memoryWord a.2.2.1) before ∧
      right.read before = .ok (memoryWord b.2.2.1) before ∧
      destination.read before = .ok (memoryWord c.2.2.1) before ∧
      Reference.Sail.run (destination.write (memoryWord c.2.2.2)) before = .ok () after := by
  cases history with
  | cons past destination dm da dr dw =>
    cases past with
    | cons past right rm ra rr rw =>
      cases past with
      | cons empty left lm la lr lw =>
        cases empty with
        | nil =>
          have first := cell_write_same lr
          rw [firstReadonly] at first
          have same := (EStateM.Result.ok.inj (first.symm.trans lw)).2
          subst_vars
          have second := cell_write_same rr
          rw [secondReadonly] at second
          have same := (EStateM.Result.ok.inj (second.symm.trans rw)).2
          subst_vars
          exact ⟨left, right, destination, lm, rm, dm, la, ra, da, lr, rr, dr, dw⟩

/-- Group the already-derived Sail transfers into complete instruction rows.
    Initial state, public bytes and native logical matching remain the inputs. -/
theorem decoded_row_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : Trace.programImage before addresses = some program)
    (decoded : Decoded trace program) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        before after ∧ SailStateMatches cells history after := by
  obtain ⟨history, events, seed, after, consistent, combined, permutation, execution, final⟩ :=
    decoded_sail_history hp inverse accepted boundary image domain aligned programImage decoded
  obtain ⟨rows, rowPermutation, rowSorted, sorted, eventPermutation⟩ :=
    native_row_order hp inverse accepted boundary
  have eventsSorted : MemoryAccessList.isTimestampSorted events := by
    have full : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val) := by
      simpa only [combined] using history.property
    exact (List.pairwise_append.mp full).1
  have same := List.Perm.eq_of_pairwise' sorted eventsSorted (eventPermutation.trans permutation.symm)
  exact ⟨history, rows, after, consistent, rowPermutation, rowSorted, same.symm ▸ execution, final⟩

end Airbender.Trace.Proofs
