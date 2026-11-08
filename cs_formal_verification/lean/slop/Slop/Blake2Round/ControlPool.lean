import Slop.Blake2Round.ExclusiveMask
import Slop.Delegation.CallPaths
import Human.Trace.Workers.Blake2Round.Call

namespace Airbender.Blake2Round.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure ControlMatchingInputs [Fact p.Prime] (data : Delegation.MemoryData p) (flags : Fin 8) : Prop where
  facts : Trace.Proofs.Transfer.Facts (Delegation.Proofs.transferData data)
  distinct : (data.initial.map MemoryToken.address).Nodup
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  source : ∃ token ∈ data.initial, token.address = (Cell.register 12).addressCode ∧
    token.word = controlAt flags 0
  roundsBound : data.rows.length ≤ 10

private theorem control_next (flags : Fin 8) {i : Nat} (bound : i < 10) :
    Control.next (controlAt flags i) = controlAt flags (i + 1) := by
  have flagBound := flags.isLt
  interval_cases i
  all_goals simp [Control.next, controlAt]
  all_goals omega

private theorem control_iterate (flags : Fin 8) {i : Nat} (bound : i ≤ 10) :
    Control.next^[i] (controlAt flags 0) = controlAt flags i := by
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

private theorem call_path [Fact p.Prime] {data : Delegation.MemoryData p} {flags : Fin 8}
    (inputs : ControlMatchingInputs data flags) :
    ∃ source : MemoryToken p, ∃ path : List (MemoryToken p),
      path.length = data.rows.length + 1 ∧ path.head? = some source ∧
      source.word = controlAt flags 0 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[42],
          row.writeToken importedConstraintsMemoryPorts[42])) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, sourceMember, sourceCode, initialWord⟩ := inputs.source
  obtain ⟨sink, sinkMember, sinkAddress, path, head, last, _, matching⟩ :=
    Trace.Proofs.keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      inputs.facts.matching inputs.facts.addresses inputs.distinct inputs.facts.order source sourceMember
  have ordered := Trace.Proofs.rank_ordered (fun token : MemoryToken p => (timeOfPair token.time).value) path
    (fun edge member => inputs.facts.order edge (List.mem_of_mem_filter (matching.mem_iff.mp member)))
  rw [sourceCode] at matching
  change (path.zip path.tail).Perm
    (data.steps.filter fun edge => edge.1.address = (Cell.register 12).addressCode) at matching
  rw [control_edges inputs.family] at matching
  have length : path.length = data.rows.length + 1 := by
    have equal := matching.length_eq
    have positive : 0 < path.length := by cases path <;> simp_all
    simp only [List.length_zip, List.length_tail, List.length_map] at equal
    omega
  exact ⟨source, path, length, head, initialWord, ordered, matching, sink, sinkMember,
    sinkAddress.trans sourceCode, last⟩

private theorem scheduled_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : ControlMatchingInputs data flags) :
    ∃ path : List (MemoryToken p), path.length = data.rows.length + 1 ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (data.rows.map fun row =>
        (readToken row.assignment importedConstraintsMemoryPorts[42],
          row.writeToken importedConstraintsMemoryPorts[42])) ∧
      (∀ (i : Nat) (bound : i < path.length), (path[i]'bound).word = controlAt flags i) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        path.getLast? = some sink := by
  obtain ⟨source, path, length, head, initialWord, ordered, matching, terminal⟩ := call_path inputs
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
  refine ⟨path, length, ordered, matching, ?_, terminal⟩
  intro i bound
  have count := inputs.roundsBound
  rw [sequence i bound, initialWord, control_iterate flags (by omega)]

theorem matching_rounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : ControlMatchingInputs data flags) :
    ∀ row ∈ data.rows, ∃ round : Fin 10, Memory.RoundMask row.assignment round ∧
      (row.assignment Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val := by
  have count := inputs.roundsBound
  obtain ⟨path, length, _, matching, sequence, _⟩ := scheduled_path hp accepted inputs
  intro row rowMember
  have edgeMember : (readToken row.assignment importedConstraintsMemoryPorts[42],
      row.writeToken importedConstraintsMemoryPorts[42]) ∈ path.zip path.tail :=
    matching.mem_iff.mpr (List.mem_map.mpr ⟨row, rowMember, rfl⟩)
  obtain ⟨i, bound, sameEdge⟩ := List.mem_iff_getElem.mp edgeMember
  simp only [List.length_zip, List.length_tail] at bound
  have iBound : i < 10 := by omega
  have readWord := congrArg (fun edge => edge.1.word) sameEdge
  have scheduled := sequence i (by omega)
  have word : (readToken row.assignment importedConstraintsMemoryPorts[42]).word = controlAt flags i := by
    simp only [List.getElem_zip, List.getElem_tail] at readWord
    exact readWord.symm.trans scheduled
  have high := congrArg Word.hi word
  have power : 2 ^ i < 1024 := by interval_cases i <;> decide
  have high : (row.assignment Variables.controlReadHi).val = flags.val + 8 * (2 ^ i % 1024) := by
    simpa [readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode,
      WordColumns.code, pairCode, controlAt, Variables.controlReadHi] using high
  have high : (row.assignment Variables.controlReadHi).val = flags.val + 8 * 2 ^ i := by
    simpa only [Nat.mod_eq_of_lt power] using high
  exact ⟨⟨i, iBound⟩, exclusive_mask (by dsimp [timestampBase] at hp; omega)
    (by
      have holds := accepted.constraints row rowMember
      simp only [Delegation.Row.constraints, inputs.family row rowMember,
        inputs.tables, Delegation.modeledSetup] at holds
      exact Verification.holds_of_sublist holds (List.sublist_append_left
        (importedConstraints setupTable) importedConstraintsTimestampLookups))
    flags ⟨i, iBound⟩ high, high⟩

theorem matching_masks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : ControlMatchingInputs data flags) :
    CallMasks data := by
  intro row member
  obtain ⟨round, mask, _⟩ := matching_rounds hp accepted inputs row member
  exact ⟨round, mask⟩

end Airbender.Blake2Round.Proofs
