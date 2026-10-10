import Airbender.Review.Keccak.Call
import Airbender.Proofs.Keccak.Schedule
import Airbender.Proofs.Delegation.Memory

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
    {setup : Table (ZMod p) (fields 8)} {path : List (MemoryToken p)}
    (size : path.length = 650) (start : path.head? = some (Cell.initialToken (p := p) (.register 10) 0))
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
      have first : (path[0]'(by omega)) = Cell.initialToken (p := p) (.register 10) 0 := by
        have head : path[0]? = some (Cell.initialToken (p := p) (.register 10) 0) := by
          simpa only [List.head?_eq_getElem?] using start
        simpa [List.getElem?_eq_getElem, size] using head
      rw [first]
      simp [schedule_start, MemoryToken.word, Cell.initialToken, Word.ofBitVec]
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

theorem call_control [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) : CallControl data := by
  obtain ⟨source, sourceMember, value, read, sourceCode⟩ :=
    image_cell_source inputs.memory.initialization (.register 10) inputs.controlCell
  have zero := (EStateM.Result.ok.inj (read.symm.trans inputs.controlStart)).1
  subst value
  subst source
  obtain ⟨sink, sinkMember, address, path, head, last, ordered, matching⟩ :=
    (Delegation.Proofs.memory_effects hp accepted inputs.memory).paths _ sourceMember
  have edges : (path.zip path.tail).Perm
      (data.rows.map fun row => (readToken row.assignment importedConstraintsMemoryPorts[0],
        row.writeToken importedConstraintsMemoryPorts[0])) := by
    change (path.zip path.tail).Perm
      (data.steps.filter fun edge => edge.1.address = (Cell.register 10).addressCode) at matching
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
  have schedule := forced_path (by dsimp [timestampBase] at hp; omega) length head checks
  have lastToken : (path[649]'(by omega)) = sink := by
    simpa [List.getLast?_eq_getElem?, length] using last
  refine ⟨sink, sinkMember, address, ?_⟩
  have result := schedule (649 : Fin 650)
  change (path[649]'(by omega)).word = Word.mk (scheduleControl 649).packed 0 at result
  rw [lastToken] at result
  simpa [schedule_finish, Word.ofBitVec, limbBase] using result

end Airbender.Keccak.Proofs
