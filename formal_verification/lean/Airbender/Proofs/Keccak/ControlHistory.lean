import Airbender.Proofs.Keccak.BoundaryInputs
import Airbender.Review.Trace.Workers.Keccak.Call
import Airbender.Proofs.Keccak.Schedule
import Airbender.Proofs.Delegation.Memory
import Airbender.Proofs.Delegation.CallPaths

namespace Airbender.Keccak.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem control_edges [Fact p.Prime] {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .keccak) :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 10).addressCode) =
      data.rows.map (fun row => (readToken row.assignment importedConstraintsMemoryPorts[0],
        row.writeToken importedConstraintsMemoryPorts[0])) := by
  simp only [Delegation.MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ member
    change kind = .keccak at same
    subst kind
    simp [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair]

private theorem forced_path [Fact p.Prime] (hp : 4096 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {path : List (MemoryToken p)} {source : MemoryToken p}
    (size : path.length = 650) (start : path.head? = some source) (startWord : source.word = ⟨0, 0⟩)
    (steps : ∀ edge ∈ path.zip path.tail, ∃ w : Nat → ZMod p,
      FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup) ∧ w 0 = 1 ∧
      edge.1.word = Word.mk (w 3).val (w 4).val ∧ edge.2.word = Word.mk (w 5).val (w 6).val) :
    ∀ i : Fin 650, (path[i.val]'(by omega)).word = ⟨(scheduleControl i).packed, 0⟩ := by
  intro i
  have establish : ∀ (n : Nat) (bound : n < 650), (path[n]'(by omega)).word =
      Word.mk (scheduleControl ⟨n, by omega⟩).packed 0 := by
    intro n
    induction n with
    | zero =>
      intro bound
      have first : (path[0]'(by omega)) = source := by
        have head : path[0]? = some source := by
          simpa only [List.head?_eq_getElem?] using start
        simpa [List.getElem?_eq_getElem, size] using head
      rw [first, startWord]
      simp [schedule_start]
    | succ n ih =>
      intro bound
      have prior := ih (by omega)
      have edge : (path[n]'(by omega), path[n + 1]'(by omega)) ∈ path.zip path.tail := by
        apply List.mem_iff_getElem.mpr
        refine ⟨n, by simp [size]; omega, ?_⟩
        simp
      obtain ⟨w, holds, active, read, write⟩ := steps _ edge
      have high := control_high_zero holds
      have current : (w 3).val = (scheduleControl ⟨n, by omega⟩).packed := by
        exact congrArg Word.lo (read.symm.trans prior)
      have next := forced_schedule_step hp ⟨n, by omega⟩ holds active current
      rw [write, next, high.2, ZMod.val_zero]
  exact establish i.val i.isLt

private theorem call_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells) :
    ∃ sink ∈ data.terminal, sink.address = (Cell.register 10).addressCode ∧
      ∃ path : List (MemoryToken p), ∃ size : path.length = 650, path.getLast? = some sink ∧
        (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
        (path.zip path.tail).Perm (data.rows.map fun row =>
          (readToken row.assignment importedConstraintsMemoryPorts[0],
            row.writeToken importedConstraintsMemoryPorts[0])) ∧
        ∀ i : Fin 650, (path[i.val]'(by have := i.isLt; omega)).word =
          ⟨(scheduleControl i).packed, 0⟩ := by
  obtain ⟨source, sourceMember, value, read, sourceCode, sourceWord⟩ :=
    Delegation.Proofs.boundary_cell_source inputs.memory inputs.controlCell
  have zero := (EStateM.Result.ok.inj (read.symm.trans inputs.controlStart)).1
  subst value
  change source.word = ⟨0, 0⟩ at sourceWord
  obtain ⟨sink, sinkMember, address, path, head, last, ordered, matching⟩ :=
    (Delegation.Proofs.memory_effects hp accepted inputs.memory).paths _ sourceMember
  have edges : (path.zip path.tail).Perm
      (data.rows.map fun row => (readToken row.assignment importedConstraintsMemoryPorts[0],
        row.writeToken importedConstraintsMemoryPorts[0])) := by
    rw [sourceCode] at matching
    rw [control_edges inputs.family] at matching
    exact matching
  have length : path.length = 650 := by
    have count := edges.length_eq
    have positive : 0 < path.length := by
      cases path with
      | nil => simp at head
      | cons _ _ => simp
    simp only [List.length_zip, List.length_tail, List.length_map, inputs.calls] at count
    omega
  have checks : ∀ edge ∈ path.zip path.tail, ∃ w : Nat → ZMod p,
      FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.setup.keccak) ∧ w 0 = 1 ∧
      edge.1.word = Word.mk (w 3).val (w 4).val ∧ edge.2.word = Word.mk (w 5).val (w 6).val := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (edges.mem_iff.mp member)
    cases row with
    | mk kind w =>
      have family := inputs.family ⟨kind, w⟩ rowMember
      change kind = .keccak at family
      subst kind
      have core := Verification.holds_of_sublist (accepted.constraints _ rowMember)
        (List.sublist_append_left (importedConstraints data.setup.keccak) importedConstraintsTimestampLookups)
      refine ⟨w, core, inputs.active _ rowMember, ?_, ?_⟩
      all_goals simp [readToken, Delegation.Row.writeToken, MemoryToken.word,
        importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, pairCode]
  exact ⟨sink, sinkMember, address.trans sourceCode, path, length, last, ordered, edges,
    forced_path (by dsimp [timestampBase] at hp; omega) length head
      sourceWord checks⟩

theorem call_control [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells) : CallControl data := by
  obtain ⟨sink, sinkMember, address, path, length, last, _, _, schedule⟩ :=
    call_path hp accepted inputs
  have lastToken : (path[649]'(by omega)) = sink := by
    simpa [List.getLast?_eq_getElem?, length] using last
  refine ⟨sink, sinkMember, address, ?_⟩
  have result := schedule (649 : Fin 650)
  change (path[649]'(by omega)).word = Word.mk (scheduleControl 649).packed 0 at result
  rw [lastToken] at result
  simpa [schedule_finish, Word.ofBitVec, limbBase] using result

theorem call_schedule [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells) :
    CallSchedule data := by
  obtain ⟨sink, sinkMember, address, path, length, last, increasing, matching, schedule⟩ :=
    call_path hp accepted inputs
  obtain ⟨ordered, perm, edges, clocks⟩ :=
    Delegation.Proofs.ordered_rows_from_path _ matching increasing
  have count : ordered.length = 649 := perm.length_eq.trans inputs.calls
  refine ⟨ordered, count, perm, clocks, ?_⟩
  intro i
  have edge : (readToken (ordered[i.val]'(by omega)).assignment importedConstraintsMemoryPorts[0],
      (ordered[i.val]'(by omega)).writeToken importedConstraintsMemoryPorts[0]) =
      (path[i.val]'(by omega), path[i.val + 1]'(by omega)) := by
    have atIndex := congrArg (fun pairs => pairs[i.val]?) edges
    simpa [List.getElem?_eq_getElem, count, length] using atIndex.symm
  have read := congrArg (fun pair => pair.1.word) edge
  have write := congrArg (fun pair => pair.2.word) edge
  constructor
  · simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code,
      importedConstraintsMemoryPorts, pairCode] using
      read.trans (schedule ⟨i.val, by have := i.isLt; omega⟩)
  · simpa [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code,
      importedConstraintsMemoryPorts, pairCode] using
      write.trans (schedule ⟨i.val + 1, by have := i.isLt; omega⟩)

end Airbender.Keccak.Proofs
