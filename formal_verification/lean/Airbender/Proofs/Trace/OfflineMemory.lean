import Airbender.Proofs.Trace.LatestReads

namespace Airbender.Trace.Proofs

private theorem dropLast_zip_tail {S : Type} (path : List S) :
    path.dropLast.zip path.tail = path.zip path.tail := by
  induction path with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail =>
      simpa only [List.dropLast_cons_cons, List.tail_cons, List.zip_cons_cons] using
        congrArg (List.cons (first, next)) ih

private theorem reversed_edges {S : Type} (path : List S) :
    (path.reverse.zip path.reverse.tail).map Prod.swap = (path.zip path.tail).reverse := by
  have backwardLast : path.reverse.dropLast = path.tail.reverse := by
    simpa only [List.reverse_reverse] using
      (congrArg List.reverse (List.tail_reverse (l := path.reverse))).symm
  have reversed : (path.dropLast.zip path.tail).reverse =
      path.dropLast.reverse.zip path.tail.reverse := by
    simpa only [List.zip_eq_zipWith] using
      (List.reverse_zipWith (f := Prod.mk) (by simp))
  rw [← dropLast_zip_tail path.reverse, backwardLast, List.tail_reverse]
  rw [List.zip_swap, ← reversed, dropLast_zip_tail]

-- Most recent cell first. The last cell is initialized by an actual zero-read
-- write; real access times are shifted by one to leave time zero for that write.
private def cellEvents {S : Type} (address : Nat) (rank value : S → Nat) :
    List S → List MemoryAccess
  | [] => []
  | [source] => [(0, address, 0, value source)]
  | current :: previous :: rest =>
      (rank current + 1, address, value previous, value current) ::
        cellEvents address rank value (previous :: rest)

private theorem cell_last_write {S : Type} (address : Nat) (rank value : S → Nat)
    (first : S) (rest : List S)
    (sorted : MemoryAccessList.isTimestampSorted (cellEvents address rank value (first :: rest))) :
    MemoryAccessList.lastWriteValue (cellEvents address rank value (first :: rest))
      sorted address = value first := by
  cases rest <;> simp [cellEvents, MemoryAccessList.lastWriteValue]

/-- A cell path is a Clean online-consistent access history, including its
    explicit initialization write. No desired read or final value is supplied. -/
theorem cell_history {S : Type} (address : Nat) (rank value : S → Nat)
    (first : S) (rest : List S)
    (ordered : (first :: rest).Pairwise (fun current previous => rank previous < rank current)) :
    ∃ sorted : MemoryAccessList.isTimestampSorted (cellEvents address rank value (first :: rest)),
      MemoryAccessList.isConsistentOnline (cellEvents address rank value (first :: rest)) sorted ∧
      ∀ event ∈ cellEvents address rank value (first :: rest), event.1 ≤ rank first + 1 := by
  induction rest generalizing first with
  | nil =>
    refine ⟨by simp [cellEvents, MemoryAccessList.isTimestampSorted], ?_, ?_⟩
    · simp [cellEvents, MemoryAccessList.isConsistentOnline, MemoryAccessList.lastWriteValue]
    · intro event member
      simp only [cellEvents, List.mem_singleton] at member
      subst event
      simp
  | cons previous tail ih =>
    have pairwise := List.pairwise_cons.mp ordered
    have growth := pairwise.1 previous (List.mem_cons_self)
    obtain ⟨restSorted, consistent, bounds⟩ := ih previous pairwise.2
    have sorted : MemoryAccessList.isTimestampSorted
        (cellEvents address rank value (first :: previous :: tail)) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, restSorted⟩
      intro event member
      have earlier := bounds event member
      change event.1 < rank first + 1
      omega
    refine ⟨sorted, ?_, ?_⟩
    · change value previous = MemoryAccessList.lastWriteValue
        (cellEvents address rank value (previous :: tail)) restSorted address ∧ _
      exact ⟨(cell_last_write address rank value previous tail restSorted).symm, consistent⟩
    · intro event member
      simp only [cellEvents, List.mem_cons] at member
      rcases member with rfl | inRest
      · exact Nat.le_refl _
      · have earlier := bounds event inRest
        omega

private theorem cell_events_projection {S : Type} (address : Nat) (rank value : S → Nat)
    (path : List S) :
    cellEvents address rank value path =
      (path.zip path.tail).map (fun edge =>
        ((rank edge.1 + 1, address, value edge.2, value edge.1) : MemoryAccess)) ++
      path.getLast?.toList.map (fun source => ((0, address, 0, value source) : MemoryAccess)) := by
  induction path with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons previous tail =>
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.getLast?_cons_cons]
      change (rank first + 1, address, value previous, value first) ::
          cellEvents address rank value (previous :: tail) =
        ((rank first + 1, address, value previous, value first) ::
          ((previous :: tail).zip tail).map (fun edge =>
            (rank edge.1 + 1, address, value edge.2, value edge.1))) ++
          (previous :: tail).getLast?.toList.map (fun source => (0, address, 0, value source))
      rw [List.cons_append, ih]
      rfl

/-- The Clean event is exactly the native port, with its clock shifted by one. -/
theorem transfer_event [Fact p.Prime] (hp : timestampBase < p)
    (row : Row p) (port : MemoryPort) (member : port ∈ row.ports)
    (initial : (decodeTimestamp row.assignment row.columns.initialTime).Bounded)
    (aligned : (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0) :
    transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port) =
      ((port.event row.columns row.assignment).1 + 1, port.address.code row.assignment,
        port.readCode row.assignment, port.writeCode row.assignment) := by
  have canonical := (write_time hp (base := rawPair row.assignment row.columns.initialTime)
    initial aligned (port_offset row port member)).2
  change ((timeOfPair ((rawPair row.assignment row.columns.initialTime).1 + (port.clock.offset : ZMod p),
    (rawPair row.assignment row.columns.initialTime).2)).value + 1, _, _, _) = _
  rw [canonical]
  rfl

theorem native_cell_histories [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ history, CellHistory trace source history := by
  intro source member
  obtain ⟨path, head, _, ordered, permutation⟩ :=
    native_memory_paths hp inverse accepted boundary unique source member
  let rank := fun token : MemoryToken p => (timeOfPair token.time).value
  let project : MemoryToken p × MemoryToken p → MemoryAccess := fun edge =>
    (rank edge.2 + 1, source.address, edge.1.value, edge.2.value)
  let initialization : List MemoryAccess := [(0, source.address, 0, source.value)]
  have backwardOrder : path.reverse.Pairwise (fun current previous => rank previous < rank current) :=
    List.pairwise_reverse.mpr (List.pairwise_map.mp ordered)
  have backwardLast : path.reverse.getLast? = some source := by
    rw [List.getLast?_reverse, head]
  have projected : cellEvents source.address rank MemoryToken.value path.reverse =
      (path.zip path.tail).reverse.map project ++ initialization := by
    rw [cell_events_projection]
    have edges := congrArg (List.map project) (reversed_edges path)
    simp only [List.map_map, Function.comp_def, project, Prod.swap] at edges
    have initialized : path.reverse.getLast?.toList.map
        (fun cell : MemoryToken p => ((0, source.address, 0, cell.value) : MemoryAccess)) =
        initialization := by
      rw [backwardLast]
      rfl
    exact congrArg₂ (fun left right : List MemoryAccess => left ++ right) edges initialized
  have projectNative :
      (trace.memorySteps.filter fun edge => edge.1.address = source.address).map project =
      (trace.memorySteps.filter fun edge => edge.1.address = source.address).map transferEvent := by
    apply List.map_congr_left
    intro edge edgeMember
    have addressEq : edge.1.address = source.address :=
      of_decide_eq_true (List.mem_filter.mp edgeMember).2
    simp only [project, transferEvent, rank, addressEq]
  have projectedPermutation : ((path.zip path.tail).reverse.map project).Perm
      ((trace.memorySteps.filter fun edge => edge.1.address = source.address).map transferEvent) := by
    rw [← projectNative]
    exact ((List.reverse_perm _).map project).trans (permutation.map project)
  cases reverseEq : path.reverse with
  | nil =>
    have empty : path = [] := List.reverse_eq_nil_iff.mp reverseEq
    simp [empty] at head
  | cons first rest =>
    rw [reverseEq] at backwardOrder
    obtain ⟨sorted, consistent, _⟩ := cell_history source.address rank MemoryToken.value
      first rest backwardOrder
    refine ⟨⟨cellEvents source.address rank MemoryToken.value (first :: rest), sorted⟩, ?_, consistent⟩
    change List.Perm (cellEvents source.address rank MemoryToken.value (first :: rest)) _
    rw [reverseEq] at projected
    rw [projected]
    exact (projectedPermutation.append_right _).trans (List.perm_append_comm)

end Airbender.Trace.Proofs
