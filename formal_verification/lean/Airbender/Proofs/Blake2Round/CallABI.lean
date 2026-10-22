import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeCall
import Airbender.Proofs.Blake2Round.CallExecution
import Airbender.Proofs.Blake2Round.PointerHistory
import Airbender.Proofs.Delegation.AtomicHistory

namespace Airbender.Blake2Round.Call.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem round_power_bound (round : Fin 10) : 2 ^ round.val < 1024 := by
  fin_cases round <;> decide

theorem native_core [Fact p.Prime]
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    {w : Nat → ZMod p} (member : (⟨.blakeRound, w⟩ : Delegation.Row p) ∈ data.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable) := by
  have holds := accepted.constraints _ member
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  exact Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setupTable) importedConstraintsTimestampLookups)

theorem pointer_conditions [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {w : Nat → ZMod p} (member : (⟨.blakeRound, w⟩ : Delegation.Row p) ∈ data.rows)
    {round : Fin 10} (mask : Memory.RoundMask w round) :
    (ROM.limit ≤ (Native.input round w).statePointer.toBitVec.toNat ∧
      ROM.limit ≤ (Native.input round w).messagePointer.toBitVec.toNat) ∧
    ((Native.input round w).statePointer.toBitVec.toNat % 128 = 0 ∧
      (Native.input round w).messagePointer.toBitVec.toNat % 64 = 0) ∧
    (Native.input round w).statePointer.toBitVec ≠ (Native.input round w).messagePointer.toBitVec := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have operation := Blake2Round.Proofs.call_operation_inputs clockBound accepted inputs
  have bounds := Delegation.Proofs.operation_word_bounds_at_boundary hp inverse accepted operation
  have core := native_core accepted inputs member
  have portMember (i : Fin 43) : importedConstraintsMemoryPorts[i] ∈
      (⟨.blakeRound, w⟩ : Delegation.Row p).ports := Array.getElem_mem i.isLt
  have effect := Native.Proofs.native_effects hp inverse round core mask
    (fun port present => bounds.reads _ member port (by
      change port ∈ importedConstraintsMemoryPorts
      exact present))
  have initialized (port : MemoryPort) (present : port ∈ importedConstraintsMemoryPorts) :
      ∃ cell : Cell, cell.addressCode = port.address.code w := by
    have step : (readToken w port, (⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port) ∈ data.steps :=
      List.mem_flatMap.mpr ⟨_, member, List.mem_map.mpr ⟨port, by
        change port ∈ importedConstraintsMemoryPorts.toList
        simpa using present, rfl⟩⟩
    obtain ⟨cell, _, code⟩ := Delegation.Proofs.initialized_cell clockBound accepted inputs.memory step
    exact ⟨cell, code⟩
  have codes := cells_projection effect.2.2.2 initialized
  have tracked (i : Fin 43) : (cells (Native.input round w))[i] ∈ domain :=
    Delegation.Proofs.port_initialized_cell clockBound accepted inputs.memory member (portMember i) (codes i).symm
  have stateBound : (Native.input round w).statePointer.Bounded := bounds.reads _ member _ (portMember 0)
  have messageBound : (Native.input round w).messagePointer.Bounded := bounds.reads _ member _ (portMember 25)
  have compatible : SerializedInverse.Scale128 p := by linear_combination inverse
  have alignment := Blake2Round.Proofs.pointer_alignment (p := p) (setup := setupTable) (w := w) hp compatible core
  have mapping := Native.Proofs.native_mapping round core
  refine ⟨⟨ram _ (by simpa [cells, Fin.getElem_fin] using tracked 1),
    ram _ (by simpa [cells, Fin.getElem_fin] using tracked 26)⟩, ?_, ?_⟩
  · rw [Word.toBitVec_toNat stateBound, Word.toBitVec_toNat messageBound,
      mapping.statePointer, mapping.messagePointer]
    simpa [Word.value, limbBase, Nat.add_mod, Nat.mul_mod] using alignment
  · intro equal
    let addresses := ((⟨.blakeRound, w⟩ : Delegation.Row p).memorySteps.map fun edge => edge.1.address)
    have left : addresses.get ⟨1, by change 1 < 43; decide⟩ =
        importedConstraintsMemoryPorts[1].address.code w := rfl
    have right : addresses.get ⟨26, by change 26 < 43; decide⟩ =
        importedConstraintsMemoryPorts[26].address.code w := rfl
    have leftCode : (Cell.ram (Native.input round w).statePointer.toBitVec).addressCode =
        importedConstraintsMemoryPorts[1].address.code w := by
      simpa [cells, Fin.getElem_fin] using codes 1
    have rightCode : (Cell.ram (Native.input round w).messagePointer.toBitVec).addressCode =
        importedConstraintsMemoryPorts[26].address.code w := by
      simpa [cells, Fin.getElem_fin] using codes 26
    have matched := (leftCode.symm.trans (congrArg (fun address => (Cell.ram address).addressCode) equal)).trans rightCode
    have same : addresses.get ⟨1, by change 1 < 43; decide⟩ =
        addresses.get ⟨26, by change 26 < 43; decide⟩ := by
      exact (left.trans matched).trans right.symm
    have unique := Delegation.Proofs.row_addresses_distinct clockBound accepted inputs.memory member
    have impossible := congrArg Fin.val (unique.get_inj_iff.mp same)
    norm_num at impossible

theorem derived_control [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    {row : Delegation.Row p} (member : row ∈ data.rows) :
    ∃ round : Fin 10, Memory.RoundMask row.assignment round ∧
      (Native.input round row.assignment).controller =
        ⟨0, Call.flags (Native.input round row.assignment) + 8 * 2 ^ round.val⟩ ∧
      round.val < if (Native.input round row.assignment).reducedRounds then 7 else 10 := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨ordered, permutation, _, controls, _⟩ :=
    Blake2Round.Proofs.ordered_controls clockBound accepted inputs
  obtain ⟨i, bound, same⟩ := List.mem_iff_getElem.mp (permutation.mem_iff.mpr member)
  have indexBound : i < if flags.val % 2 = 1 then 7 else 10 := by
    rw [← inputs.calls, ← permutation.length_eq]
    exact bound
  have indexTen : i < 10 := by split_ifs at indexBound <;> omega
  let round : Fin 10 := ⟨i, indexTen⟩
  have control := (controls i bound).1
  rw [same] at control
  have packed : (Native.input round row.assignment).controller = ⟨0, flags.val + 8 * 2 ^ round.val⟩ := by
    have powerBound : 2 ^ i < 1024 := round_power_bound round
    change (readToken row.assignment importedConstraintsMemoryPorts[42]).word = ⟨0, flags.val + 8 * 2 ^ i⟩
    simpa only [controlAt, Nat.mod_eq_of_lt powerBound] using control
  have modes := Blake2Round.Proofs.call_modes clockBound accepted inputs row member round
  have recovered : Call.flags (Native.input round row.assignment) = flags.val := by
    rw [Call.flags, modes.1, modes.2.1, modes.2.2]
    fin_cases flags <;> rfl
  have family := inputs.family row member
  have holds := accepted.constraints row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeRound at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have mapping := Native.Proofs.native_mapping round core
  have high := congrArg Word.hi (mapping.controller.inputWord.symm.trans packed)
  have mask := Blake2Round.Proofs.exclusive_mask (p := p) (setup := setupTable) (w := w)
    (by omega) core flags round high
  refine ⟨round, mask, ?_, ?_⟩
  · rw [recovered]
    exact packed
  · rw [modes.1]
    simpa only [decide_eq_true_eq] using indexBound

theorem abi_in_span [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Blake2Round.Proofs.BoundaryCallInputs data initial domain flags)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.rows) :
    ∃ round : Fin 10, Memory.RoundMask row.assignment round ∧ ABI (Native.input round row.assignment) := by
  obtain ⟨round, mask, control, bound⟩ := derived_control hp accepted inputs member
  have family := inputs.family row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeRound at family
  subst kind
  obtain ⟨ram, aligned, distinct⟩ := pointer_conditions hp inverse accepted inputs ram member mask
  exact ⟨round, mask, control, bound, ram, aligned, distinct⟩

end Airbender.Blake2Round.Call.Proofs
