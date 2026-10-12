import Airbender.Proofs.Blake2G.BoundaryInputs
import Airbender.Proofs.Blake2G.CallControl
import Airbender.Proofs.Delegation.IndexedPaths

namespace Airbender.Blake2G.Proofs
open Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem control_edges {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeG) :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) =
      data.rows.map (fun row => (readToken row.assignment importedConstraintsMemoryPorts[8],
        row.writeToken importedConstraintsMemoryPorts[8])) := by
  simp only [Delegation.MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ member
    change kind = .blakeG at same
    subst kind
    simp [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair]

private theorem call_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced) :
    ∃ source : MemoryToken p, ∃ path : List (MemoryToken p),
      path.length = data.rows.length + 1 ∧ path.head? = some source ∧
      source.word = controlAt reduced 0 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[8],
          row.writeToken importedConstraintsMemoryPorts[8])) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  have count : 0 < data.rows.length ∧ data.rows.length ≤ 80 := by
    rw [inputs.calls]; cases reduced <;> decide
  obtain ⟨first, firstMember⟩ : ∃ row, row ∈ data.rows :=
    List.exists_mem_of_ne_nil _ (by intro empty; simp [empty] at count)
  have firstFamily := inputs.family first firstMember
  have portMember : importedConstraintsMemoryPorts[8] ∈ first.ports := by
    simp [Delegation.Row.ports, firstFamily, importedConstraintsMemoryPorts]
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted inputs.memory firstMember portMember
    (cell := .register 12) (by rfl)
  obtain ⟨source, sourceMember, value, read, sourceCode, sourceWord⟩ :=
    Delegation.Proofs.boundary_cell_source inputs.memory tracked
  have same := (EStateM.Result.ok.inj (read.symm.trans inputs.controlStart)).1
  subst value
  obtain ⟨sink, sinkMember, sinkAddress, path, head, last, ordered, matching⟩ :=
    (Delegation.Proofs.memory_effects hp accepted inputs.memory).paths _ sourceMember
  rw [sourceCode] at matching
  change (path.zip path.tail).Perm
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) at matching
  rw [control_edges inputs.family] at matching
  have length : path.length = data.rows.length + 1 := by
    have equal := matching.length_eq
    have positive : 0 < path.length := by cases path <;> simp_all
    simp only [List.length_zip, List.length_tail, List.length_map] at equal
    omega
  have initialWord : source.word = controlAt reduced 0 := by
    rw [sourceWord]
    cases reduced <;> rfl
  exact ⟨source, path, length, head, initialWord, ordered, matching, sink, sinkMember,
    sinkAddress.trans sourceCode, last⟩

private theorem scheduled_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced) :
    ∃ path : List (MemoryToken p), path.length = data.rows.length + 1 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[8],
          row.writeToken importedConstraintsMemoryPorts[8])) ∧
      (∀ (i : Nat) (bound : i < path.length), (path[i]'bound).word = controlAt reduced i) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, path, length, head, initialWord, ordered, matching, terminal⟩ := call_path hp accepted inputs
  have advances : ∀ i, i + 1 < path.length → ∀ edge ∈ path.zip path.tail,
      edge.1.word = controlAt reduced i → edge.2.word = controlAt reduced (i + 1) := by
    intro i bound edge member current
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (matching.mem_iff.mp member)
    have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
        (importedConstraints (setupTable Control.controllerRows)) := by
      have holds := accepted.constraints row rowMember
      simp only [Delegation.Row.constraints, inputs.family row rowMember,
        inputs.tables, Delegation.modeledSetup] at holds
      exact Verification.holds_of_sublist holds (List.sublist_append_left
        (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
    have currentLo : (row.assignment Variables.controlReadLo).val = (controlAt reduced i).lo := by
      simpa [readToken, MemoryToken.word, importedConstraintsMemoryPorts,
        MemoryPort.readCode, WordColumns.code, pairCode, Variables.controlReadLo] using congrArg Word.lo current
    have size : i < callCount reduced := by rw [length, inputs.calls] at bound; omega
    have next := forced_control_step (by dsimp [timestampBase] at hp; omega)
      reduced i size core (inputs.active row rowMember) currentLo
    simpa [Delegation.Row.writeToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.writeCode, WordColumns.code, pairCode,
      Variables.controlWriteLo, Variables.controlWriteHi] using next
  exact ⟨path, length, ordered, matching,
    Delegation.Proofs.indexed_path_words head (controlAt reduced) initialWord advances, terminal⟩

theorem ordered_controls [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[8]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[8]).time).value) ∧
      (∀ (i : Nat) (bound : i < ordered.length),
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8]).word = controlAt reduced i ∧
        ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]).word = controlAt reduced (i + 1)) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt reduced data.rows.length := by
  obtain ⟨path, length, increasing, matching, sequence, sink, sinkMember, address, last⟩ :=
    scheduled_path hp accepted inputs
  obtain ⟨ordered, permutation, edges, clocks⟩ := Delegation.Proofs.ordered_rows_from_path _ matching increasing
  refine ⟨ordered, permutation, clocks, ?_, sink, sinkMember, address, ?_⟩
  · intro i bound
    have edge := congrArg (fun pairs => pairs[i]?) edges
    have pathBound : i + 1 < path.length := by have := permutation.length_eq; omega
    have edge : (path[i]'(by omega), path[i + 1]'pathBound) =
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8],
          (ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]) := by
      simpa [List.getElem?_eq_getElem, bound, List.length_zip, List.length_tail,
        show i < path.length - 1 by omega] using edge
    exact ⟨(congrArg (fun edge => edge.1.word) edge).symm.trans (sequence i (by omega)),
      (congrArg (fun edge => edge.2.word) edge).symm.trans (sequence (i + 1) pathBound)⟩
  · have positive : 0 < path.length := by omega
    have endToken : path[path.length - 1]'(by omega) = sink := by
      have endToken := last
      rw [List.getLast?_eq_getElem?] at endToken
      simpa [List.getElem?_eq_getElem, show path.length - 1 < path.length by omega] using endToken
    have value := sequence (path.length - 1) (by omega)
    simpa only [length, Nat.add_sub_cancel] using
      (congrArg MemoryToken.word endToken).symm.trans value

end Airbender.Blake2G.Proofs
