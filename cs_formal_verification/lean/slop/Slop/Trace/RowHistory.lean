module
public import Slop.Trace.Program
public import Slop.Trace.Values
public import Slop.Trace.ZeroValues
public import Slop.Defs.Helpers.Context.Columns
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Context.Model
public import Slop.Defs.Helpers.Memory.RowEvents
public import Slop.Defs.Helpers.Memory.History

@[expose] public section

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

abbrev rowClock (row : Row p Kind) : Nat := row.clock

theorem native_events_projection [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    trace.nativeEvents = trace.rows.flatMap (rowEvents trace.memoryEpoch) := by
  simp only [Data.nativeEvents, Data.memorySteps, List.map_flatMap]
  apply List.flatMap_congr
  intro row member
  simp only [Row.memorySteps, List.map_map, Function.comp_def, rowEvents, nativeRowEvents]
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

private theorem row_events_sorted [Fact p.Prime] [ClockLaws Kind p]
    (epoch : Nat) (row : Row p Kind) :
    MemoryAccessList.isTimestampSorted (rowEvents epoch row).reverse := by
  have decreasing : (row.ports.toList.reverse.map (fun port => port.clock.offset)).Pairwise
      (fun a b : Nat => b < a) := by
    rw [List.map_reverse, ClockLaws.offsets row]
    decide
  have portsOrdered : row.ports.toList.reverse.Pairwise
      (fun a b => b.clock.offset < a.clock.offset) :=
    (List.pairwise_map (f := fun port : MemoryPort => port.clock.offset)).mp decreasing
  change MemoryAccessList.isTimestampSorted
    (row.ports.toList.map (fun port =>
      ((epoch + (port.event row.columns row.assignment).1,
        port.address.code row.assignment, port.readCode row.assignment, port.writeCode row.assignment) : MemoryAccess))).reverse
  unfold MemoryAccessList.isTimestampSorted
  rw [← List.map_reverse]
  apply List.pairwise_map.mpr
  apply portsOrdered.imp
  intro a b less
  change epoch + ((decodeTimestamp row.assignment row.columns.initialTime).value + b.clock.offset) <
    epoch + ((decodeTimestamp row.assignment row.columns.initialTime).value + a.clock.offset)
  omega

private theorem row_events_separated [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {first last : Row p Kind} (firstMember : first ∈ trace.rows) (lastMember : last ∈ trace.rows)
    (ordered : rowClock last < rowClock first)
    {a b : MemoryAccess} (firstEvent : a ∈ (rowEvents trace.memoryEpoch first).reverse)
    (lastEvent : b ∈ (rowEvents trace.memoryEpoch last).reverse) : b.1 < a.1 := by
  obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp firstEvent)
  obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp lastEvent)
  have lo := port_offset first left (by simpa using leftMember)
  have ro := port_offset last right (by simpa using rightMember)
  have fa : rowClock first % 4 = 0 := by
    simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using
      (clock_inputs hp inverse accepted boundary first firstMember).aligned
  have la : rowClock last % 4 = 0 := by
    simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using
      (clock_inputs hp inverse accepted boundary last lastMember).aligned
  change trace.memoryEpoch + (rowClock last + right.clock.offset) <
    trace.memoryEpoch + (rowClock first + left.clock.offset)
  omega

/-- Strict clocks give an instruction ordering, and each instruction's three
    accesses stay together. Neither witness row order nor expected reads are used. -/
theorem native_row_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∃ rows : List (Row p Kind), rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      MemoryAccessList.isTimestampSorted
        (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) ∧
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
  let rows := trace.rows.mergeSort (fun a b => decide (rowClock b ≤ rowClock a))
  have permutation : rows.Perm trace.rows := List.mergeSort_perm _ _
  have weak : rows.Pairwise (fun a b => rowClock b ≤ rowClock a) := by
    have sorted := List.pairwise_mergeSort
      (le := fun a b : Row p Kind => decide (rowClock b ≤ rowClock a))
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
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {rows : List (Row p Kind)} (permutation : rows.Perm trace.rows)
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

end Airbender.Trace.Proofs
