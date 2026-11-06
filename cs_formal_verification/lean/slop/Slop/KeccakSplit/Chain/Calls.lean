import Slop.KeccakSplit.Chain.Paths
import Slop.KeccakSplit.Chain.Atomic
import Slop.KeccakSplit.Reference.Executions
import Slop.Delegation.CallHistory

/- A complete initialized request: the control path orders the 361 rows, the Sail
   history splits into one atomic group per row, and each row executes its call
   between consecutive group boundaries. -/

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- Every lane slot 0..29 is accessed by some call. -/
theorem slot_coverage : ∀ slot : Fin 30, ∃ index : Fin 361, ∃ lane : Fin 7,
    lane.val < Call.slotCount (kindAt index.val) ∧ ((Call.slots index)[lane]).val = slot.val := by
  decide +kernel

theorem port_time (row : Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 =
      (timeOfPair (controlEdge row).2.time).value + 1 := by
  have same : (row.writeToken port).time = (row.writeToken (controlPort row.kind)).time := by
    change (_, _) = (_, _)
    rw [port_offset row present, port_offset row (control_port_member row)]
  simp only [transferEvent, controlEdge, same]

theorem get_index_eq {α : Type} {l : List α} {a b : Nat} (same : a = b) {ha : a < l.length}
    {hb : b < l.length} : l[a]'ha = l[b]'hb := by
  subst same; rfl

theorem readWord_eq (row : Row p) {index : Nat} (bound : index < row.ports.size) :
    row.readWord index = (readToken row.assignment row.ports[index]).word := by
  simp [Row.readWord, bound]

/-- Ports 0 and 1 of every worker are x10 and x11. -/
theorem register_ports (row : Row p) :
    (∃ bound : 0 < row.ports.size, (row.ports[0]).address = .constantRegister 10) ∧
      (∃ bound : 1 < row.ports.size, (row.ports[1]).address = .constantRegister 11) := by
  cases row with
  | mk kind w =>
    cases kind <;>
      exact ⟨⟨by simp only [Row.ports]; decide, rfl⟩, ⟨by simp only [Row.ports]; decide, rfl⟩⟩

/-- The call chain of a complete request, with its pointer, initial lane reads and
    final memory agreement. -/
theorem call_chain (contract : RowContract) (control : Split.Proofs.ControlFacts babyBearModulus)
    {data : MemoryData babyBearModulus} {initial : State} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : CallInputs data initial cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (states : Fin 362 → State) (pointer : BitVec 32),
      states 0 = initial ∧
      (∀ index : Fin 361, Call.ExecutesAt index (states index.castSucc) (states index.succ)) ∧
      (Cell.register 11).read (states 0) = .ok pointer (states 0) ∧
      (∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
        (Call.laneCell pointer ⟨slot.val, by omega⟩ high).read (states 0) = .ok value (states 0)) ∧
      TraceMapping data initial (states 361) cells := by
  have hp := babyBear_clock
  have active := inputs.active
  have boundary := inputs.memory.toBoundaryInputs
  have facts := transfer_facts hp control accepted active boundary
  have reads := fun {row} (member : row ∈ data.rows) =>
    row_reads_bounded contract control accepted active inputs.memory member
  -- the x10 seed holds 0
  obtain ⟨source, sourceMember, sourceCode, sourceRead, sourceWord⟩ :=
    Transfer.native_cell_source boundary.toNativeInputs inputs.controlCell
  have zero := (EStateM.Result.ok.inj (sourceRead.symm.trans inputs.controlStart)).1
  rw [zero] at sourceWord
  change source.word = ⟨0, 0⟩ at sourceWord
  -- the control path orders the rows
  obtain ⟨path, head, increasing, matching⟩ :=
    control_path hp control accepted active boundary sourceMember sourceCode
  have pathLength : path.length = 362 := by
    have count := matching.length_eq
    have positive : 0 < path.length := by
      cases path with
      | nil => simp at head
      | cons _ _ => simp
    simp only [List.length_zip, List.length_tail, List.length_map, inputs.calls] at count
    omega
  have steps : ∀ edge ∈ path.zip path.tail, edge.2.word = advance edge.1.word := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (matching.mem_iff.mp member)
    obtain ⟨index, _, readControl, writeControl, _⟩ :=
      contract.effects row (accepted.constraints row rowMember) (active row rowMember) (reads rowMember)
    rw [← (control_words row).1, ← (control_words row).2, readControl, writeControl]
    rfl
  have words := Delegation.Proofs.path_word_sequence head advance steps
  obtain ⟨ordered, perm, edges, clocks⟩ :=
    Delegation.Proofs.ordered_rows_from_path controlEdge matching increasing
  have count : ordered.length = 361 := perm.length_eq.trans inputs.calls
  have orderedMember : ∀ (i : Nat) (bound : i < ordered.length), ordered[i] ∈ data.rows :=
    fun i bound => perm.mem_iff.mp (List.getElem_mem bound)
  have orderedControl : ∀ (i : Nat) (bound : i < 361),
      (ordered[i]'(by omega)).readWord 0 = ⟨controlAt i, 0⟩ := by
    intro i bound
    have edge : controlEdge (ordered[i]'(by omega)) = (path[i]'(by omega), path[i + 1]'(by omega)) := by
      have e := List.getElem_of_eq edges (i := i) (by simp [pathLength]; omega)
      simp only [List.getElem_zip, List.getElem_tail, List.getElem_map] at e
      exact e.symm
    rw [(control_words _).1, edge]
    change (path[i]'(by omega)).word = _
    rw [words i (by omega), sourceWord, advance_iterate i bound]
  -- one atomic Sail group per row, in clock order
  obtain ⟨_, events, after, bound, permutation, order, actual, final⟩ :=
    native_sail_history hp control accepted active boundary aligned
  have grouped : Delegation.Proofs.GroupedSailHistory cells
      (fun row : Row babyBearModulus => row.memorySteps.map transferEvent) ordered.reverse initial after := by
    apply Delegation.Proofs.grouped_history (fun row => (timeOfPair (controlEdge row).2.time).value + 1)
      _ _ order _ _ actual
    · apply List.pairwise_reverse.mpr
      exact clocks.imp (by intro a b less; omega)
    · have rows := List.Perm.flatMap_right (fun row : Row babyBearModulus => row.memorySteps.map transferEvent)
        ((List.reverse_perm ordered).trans perm)
      have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) =
          data.steps.map transferEvent := by
        simp only [MemoryData.steps, List.map_flatMap]
      exact permutation.trans (pooled ▸ rows).symm
    · intro row _ event present
      obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
      obtain ⟨port, member, rfl⟩ := List.mem_map.mp included
      exact port_time row (by simpa using member)
  obtain ⟨list, listCount, listHead, listLast, groupSteps⟩ := Delegation.Proofs.grouped_boundaries grouped
  have listLength : list.length = 362 := by simpa [count] using listCount
  let states : Fin 362 → State := fun k => list[361 - k.val]'(by omega)
  have stateZero : states 0 = initial := by
    have endpoint := List.getLast_of_getLast?_eq_some listLast
    simpa [states, List.getLast_eq_getElem, listLength] using endpoint
  have stateLast : states 361 = after := by
    have first : list[0]? = some after := by simpa only [List.head?_eq_getElem?] using listHead
    simpa [states, List.getElem?_eq_getElem, listLength] using first
  have rowHistory : ∀ (i : Nat) (iBound : i < 361), ∃ events : List MemoryAccess,
      events.Perm ((ordered[i]'(by omega)).memorySteps.map transferEvent) ∧
      SailHistory cells events (states ⟨i, by omega⟩) (states ⟨i + 1, by omega⟩) := by
    intro i iBound
    obtain ⟨events, eventsPerm, history⟩ := groupSteps (360 - i) (by simp [count]; omega)
    have reversed : ordered.reverse[360 - i]'(by simp [count]; omega) = ordered[i]'(by omega) := by
      rw [List.getElem_reverse]
      congr 1
      omega
    refine ⟨events, reversed ▸ eventsPerm, ?_⟩
    have left : 360 - i + 1 = 361 - i := by omega
    have right : 360 - i = 361 - (i + 1) := by omega
    have first : states ⟨i, by omega⟩ = list[360 - i + 1]'(by omega) := get_index_eq left.symm
    have second : states ⟨i + 1, by omega⟩ = list[360 - i]'(by omega) := get_index_eq right.symm
    rw [first, second]
    exact history
  -- every tracked cell stays readable
  have initialReadable : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial := by
    intro cell member
    obtain ⟨token, _, _, read, _⟩ := Transfer.native_cell_source boundary.toNativeInputs member
    exact ⟨_, read⟩
  have readable : ∀ (k : Nat) (kBound : k < 362), ∀ cell ∈ cells,
      ∃ value, cell.read (states ⟨k, kBound⟩) = .ok value (states ⟨k, kBound⟩) := by
    intro k
    induction k with
    | zero => intro _; simpa [stateZero] using initialReadable
    | succ k ih =>
      intro kBound
      obtain ⟨events, eventsPerm, history⟩ := rowHistory k (by omega)
      exact Delegation.Proofs.history_readable history aligned
        (fun event present => row_no_zero event (eventsPerm.mem_iff.mp present)) (ih (by omega))
  -- each row executes its call
  have observations : ∀ (i : Nat) (iBound : i < 361), ∀ port ∈ (ordered[i]'(by omega)).ports,
      ∃ cell ∈ cells, cell.addressCode = port.address.code (ordered[i]'(by omega)).assignment ∧
        cell.read (states ⟨i, by omega⟩) =
          .ok (readToken (ordered[i]'(by omega)).assignment port).word.toBitVec (states ⟨i, by omega⟩) := by
    intro i iBound port present
    obtain ⟨events, eventsPerm, history⟩ := rowHistory i iBound
    obtain ⟨cell, member, code, before, _⟩ :=
      row_atomic_observations hp control accepted active boundary (orderedMember i (by omega))
        history eventsPerm aligned (readable i (by omega)) port present
    exact ⟨cell, member, code, before⟩
  have registerRead : ∀ (i : Nat) (iBound : i < 361) (register : Nat) (small : register < 32) (index : Nat)
      (indexBound : index < (ordered[i]'(by omega)).ports.size),
      ((ordered[i]'(by omega)).ports[index]).address = .constantRegister register →
      (Cell.register register).read (states ⟨i, by omega⟩) =
        .ok ((ordered[i]'(by omega)).readWord index).toBitVec (states ⟨i, by omega⟩) := by
    intro i iBound register small index indexBound address
    obtain ⟨cell, _, code, read⟩ := observations i iBound _ (Array.getElem_mem indexBound)
    have same : cell = .register register := by
      apply cell_address_injective
      rw [code, address]
      simp [MemoryAddress.code, Cell.addressCode, Nat.mod_eq_of_lt small]
    rw [same] at read
    rw [readWord_eq _ indexBound]
    exact read
  have rowRegister : ∀ (i : Nat) (iBound : i < 361) (index register : Nat) (small : register < 32),
      (∃ indexBound : index < (ordered[i]'(by omega)).ports.size,
        ((ordered[i]'(by omega)).ports[index]).address = .constantRegister register) →
      (Cell.register register).read (states ⟨i, by omega⟩) =
        .ok ((ordered[i]'(by omega)).readWord index).toBitVec (states ⟨i, by omega⟩) := by
    intro i iBound index register small ⟨indexBound, address⟩
    exact registerRead i iBound register small index indexBound address
  have executes : ∀ index : Fin 361, Call.ExecutesAt index (states index.castSucc) (states index.succ) := by
    intro index
    have member := orderedMember index.val (by omega)
    have arguments : Call.ArgumentsAt index.val (states ⟨index.val, by omega⟩) := by
      refine ⟨_, _, rowRegister index.val index.isLt 0 10 (by decide) (register_ports _).1,
        rowRegister index.val index.isLt 1 11 (by decide) (register_ports _).2, ?_, ?_⟩
      · rw [orderedControl index.val index.isLt]
        simp [Word.toBitVec, Word.value]
      · have align := contract.aligned _ (accepted.constraints _ member)
        simp only [Word.toBitVec, BitVec.toNat_ofNat]
        omega
    obtain ⟨events, eventsPerm, history⟩ := rowHistory index.val index.isLt
    exact contract.executes _ index (accepted.constraints _ member) (active _ member) arguments
      (reads member) history eventsPerm (fun port present => by
        obtain ⟨cell, _, code, read⟩ := observations index.val index.isLt port present
        exact ⟨cell, code, read⟩)
  -- one pointer for the whole request
  let pointer := ((ordered[0]'(by omega)).readWord 1).toBitVec
  have pointerReads : ∀ (k : Nat) (kBound : k < 362),
      (Cell.register 11).read (states ⟨k, kBound⟩) = .ok pointer (states ⟨k, kBound⟩) := by
    intro k
    induction k with
    | zero => intro _; exact rowRegister 0 (by omega) 1 11 (by decide) (register_ports _).2
    | succ k ih =>
      intro kBound
      exact (Call.Proofs.executes_pointer (executes ⟨k, by omega⟩) (ih (by omega))).2
  have rowPointer : ∀ (k : Nat) (kBound : k < 361),
      ((ordered[k]'(by omega)).readWord 1).toBitVec = pointer := by
    intro k kBound
    exact (EStateM.Result.ok.inj ((rowRegister k kBound 1 11 (by decide) (register_ports _).2).symm.trans
      (pointerReads k (by omega)))).1
  -- every lane word is a tracked cell, so it reads in the initial state
  have laneReads : ∀ (slot : Fin 30) (high : Bool), ∃ value : BitVec 32,
      (Call.laneCell pointer ⟨slot.val, by omega⟩ high).read (states 0) = .ok value (states 0) := by
    intro slot high
    obtain ⟨index, lane, live, slotEq⟩ := slot_coverage slot
    have member := orderedMember index.val (by omega)
    have pointerBound : ((ordered[index.val]'(by omega)).readWord 1).Bounded := by
      obtain ⟨_, ⟨indexBound, _⟩⟩ := register_ports (ordered[index.val]'(by omega))
      rw [readWord_eq _ indexBound]
      exact reads member _ (Array.getElem_mem indexBound)
    obtain ⟨port, present, code⟩ := contract.addresses _ index (accepted.constraints _ member)
      (active _ member) (orderedControl index.val index.isLt) pointerBound lane live high
    have edgeMember : (readToken (ordered[index.val]'(by omega)).assignment port,
        (ordered[index.val]'(by omega)).writeToken port) ∈ data.steps :=
      List.mem_flatMap.mpr ⟨_, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩
    have origin := Trace.Proofs.keyed_origins MemoryToken.address
      (fun token => (timeOfPair token.time).value) facts.matching facts.addresses facts.order _ edgeMember
    have tracked := boundary.toNativeInputs.toBoundaryInputs.addresses.mem_iff.mp origin
    obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp tracked
    have equal : cell = Call.laneCell pointer ⟨slot.val, by omega⟩ high := by
      apply cell_address_injective
      rw [same]
      change port.address.code _ = _
      rw [code, rowPointer index.val index.isLt]
      congr 2
      exact Fin.ext slotEq
    rw [equal] at cellMember
    obtain ⟨value, read⟩ := initialReadable _ cellMember
    exact ⟨value, by rw [stateZero]; exact read⟩
  refine ⟨states, pointer, stateZero, executes, pointerReads 0 (by omega), laneReads, ?_⟩
  rw [stateLast]
  refine ⟨⟨events, permutation, actual⟩, ?_⟩
  intro token member
  exact Transfer.terminal_sail_reads_at_boundary facts boundary.toNativeInputs.toBoundaryInputs bound final
    token member

end Airbender.Keccak.Split.Native.Proofs
