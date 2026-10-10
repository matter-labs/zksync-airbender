import Airbender.Review.Blake2Round.Call
import Airbender.Proofs.Blake2Round.ExclusiveMask
import Airbender.Proofs.Delegation.CallPaths

namespace Airbender.Blake2Round.Proofs
open Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def controlWord (flags : Fin 8) (i : Nat) : Word :=
  ⟨0, flags.val + 8 * (2 ^ i % 1024)⟩

private theorem control_next (flags : Fin 8) {i : Nat} (bound : i < 10) :
    Control.next (controlWord flags i) = controlWord flags (i + 1) := by
  have flagBound := flags.isLt
  interval_cases i
  all_goals simp [Control.next, controlWord]
  all_goals omega

private theorem control_iterate (flags : Fin 8) {i : Nat} (bound : i ≤ 10) :
    Control.next^[i] (controlWord flags 0) = controlWord flags i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih (by omega), control_next flags (by omega)]

private theorem control_edges {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeRound) :
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) =
      data.rows.map (fun row => (readToken row.assignment importedConstraintsMemoryPorts[42],
        row.writeToken importedConstraintsMemoryPorts[42])) := by
  simp only [Delegation.MemoryData.steps, List.filter_flatMap, List.map_eq_flatMap]
  change (data.rows.map _).flatten = (data.rows.map _).flatten
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ member
    change kind = .blakeRound at same
    subst kind
    simp [Delegation.Row.memorySteps, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair]

private theorem call_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags) :
    ∃ path : List (MemoryToken p), path.length = data.rows.length + 1 ∧
      path.head? = some (Cell.initialToken (p := p) (.register 12)
        (BitVec.ofNat 32 ((8 + flags.val) * 65536))) ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[42],
          row.writeToken importedConstraintsMemoryPorts[42])) := by
  have count : 0 < data.rows.length ∧ data.rows.length ≤ 10 := by
    rw [inputs.calls]; split_ifs <;> decide
  obtain ⟨first, firstMember⟩ : ∃ row, row ∈ data.rows :=
    List.exists_mem_of_ne_nil _ (by intro empty; simp [empty] at count)
  have firstFamily := inputs.family first firstMember
  have portMember : importedConstraintsMemoryPorts[42] ∈ first.ports := by
    simp [Delegation.Row.ports, firstFamily, importedConstraintsMemoryPorts]
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted inputs.memory firstMember portMember
    (cell := .register 12) (by rfl)
  obtain ⟨source, sourceMember, value, read, sourceCode⟩ :=
    Trace.Proofs.image_cell_source inputs.memory.initialization (.register 12) tracked
  have same := (EStateM.Result.ok.inj (read.symm.trans inputs.controlStart)).1
  subst value
  subst source
  obtain ⟨_, _, _, path, head, _, ordered, matching⟩ :=
    (Delegation.Proofs.memory_effects hp accepted inputs.memory).paths _ sourceMember
  change (path.zip path.tail).Perm
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) at matching
  rw [control_edges inputs.family] at matching
  have length : path.length = data.rows.length + 1 := by
    have equal := matching.length_eq
    have positive : 0 < path.length := by cases path <;> simp_all
    simp only [List.length_zip, List.length_tail, List.length_map] at equal
    omega
  exact ⟨path, length, head, ordered, matching⟩

theorem call_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[42]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[42]).time).value) := by
  obtain ⟨path, _, _, increasing, matching⟩ := call_path hp accepted inputs
  obtain ⟨ordered, perm, _, clocks⟩ := Delegation.Proofs.ordered_rows_from_path _ matching increasing
  exact ⟨ordered, perm, clocks⟩

theorem call_masks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags) :
    CallMasks data := by
  have count : 0 < data.rows.length ∧ data.rows.length ≤ 10 := by
    rw [inputs.calls]; split_ifs <;> decide
  obtain ⟨path, length, head, _, matching⟩ := call_path hp accepted inputs
  have core (row : Delegation.Row p) (member : row ∈ data.rows) :
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
        (importedConstraints setupTable) := by
    have holds := accepted.constraints row member
    have family := inputs.family row member
    simp only [Delegation.Row.constraints, family, inputs.tables, Delegation.modeledSetup] at holds
    exact Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have advances : ∀ edge ∈ path.zip path.tail, edge.2.word = Control.next edge.1.word := by
    intro edge member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp (matching.mem_iff.mp member)
    have result := Control.Proofs.soundness (by dsimp [timestampBase] at hp; omega)
      setupTable _ _ row.assignment ⟨core row rowMember, ⟨rfl, rfl⟩⟩
    simpa [Control.spec, readToken, MemoryToken.word, Delegation.Row.writeToken,
      importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code, pairCode, Control.Mapping, Variables.controlReadLo, Variables.controlReadHi,
      Variables.controlWriteLo, Variables.controlWriteHi] using result.2
  have sequence := Delegation.Proofs.path_word_sequence head Control.next advances
  have initialWord : (Cell.initialToken (p := p) (.register 12)
      (BitVec.ofNat 32 ((8 + flags.val) * 65536))).word = controlWord flags 0 := by
    rw [Trace.Proofs.initial_token_word]
    have flagBound := flags.isLt
    simp [Word.ofBitVec, controlWord, limbBase, BitVec.toNat_ofNat]
    omega
  intro row rowMember
  have edgeMember : (readToken row.assignment importedConstraintsMemoryPorts[42],
      row.writeToken importedConstraintsMemoryPorts[42]) ∈ path.zip path.tail :=
    matching.mem_iff.mpr (List.mem_map.mpr ⟨row, rowMember, rfl⟩)
  obtain ⟨i, bound, sameEdge⟩ := List.mem_iff_getElem.mp edgeMember
  simp only [List.length_zip, List.length_tail] at bound
  have iBound : i < 10 := by omega
  have readWord := congrArg (fun edge => edge.1.word) sameEdge
  have scheduled := sequence i (by omega)
  rw [initialWord, control_iterate flags (by omega)] at scheduled
  have word : (readToken row.assignment importedConstraintsMemoryPorts[42]).word = controlWord flags i := by
    simp only [List.getElem_zip, List.getElem_tail] at readWord
    exact readWord.symm.trans scheduled
  refine ⟨⟨i, iBound⟩, exclusive_mask (by dsimp [timestampBase] at hp; omega)
    (core row rowMember) flags ⟨i, iBound⟩ ?_⟩
  have high := congrArg Word.hi word
  have power : 2 ^ i < 1024 := by interval_cases i <;> decide
  have high : (row.assignment Variables.controlReadHi).val = flags.val + 8 * (2 ^ i % 1024) := by
    simpa [readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode,
      WordColumns.code, pairCode, controlWord, Variables.controlReadHi] using high
  simpa only [Nat.mod_eq_of_lt power] using high

end Airbender.Blake2Round.Proofs
