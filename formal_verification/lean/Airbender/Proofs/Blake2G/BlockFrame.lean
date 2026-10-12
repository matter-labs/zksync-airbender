import Airbender.Proofs.Blake2G.StateCells
import Airbender.Proofs.Trace.MemoryFrame

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true

theorem block_word_injective (pointer : BitVec 32) (a b : Fin 16)
    (same : pointer + BitVec.ofNat 32 (4 * a.val) =
      pointer + BitVec.ofNat 32 (4 * b.val)) : a = b := by
  have bits := (BitVec.add_right_inj pointer).mp same
  have values := congrArg BitVec.toNat bits
  have ab := a.isLt
  have bb := b.isLt
  simp only [BitVec.toNat_ofNat] at values
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at values
  exact Fin.ext (by omega)

theorem aligned_block_words_distinct (state message : BitVec 32)
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (distinct : state ≠ message) (a b : Fin 16) :
    state + BitVec.ofNat 32 (4 * a.val) ≠ message + BitVec.ofNat 32 (4 * b.val) := by
  intro same
  have offset (pointer : BitVec 32) (aligned : pointer.toNat % 64 = 0) (index : Fin 16) :
      (pointer + BitVec.ofNat 32 (4 * index.val)).toNat % 64 = 4 * index.val := by
    have bound := index.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 32)]
    rw [Nat.add_mod, aligned, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 32),
      Nat.mod_eq_of_lt (by omega), Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)]
  have residue := congrArg (fun value : BitVec 32 => value.toNat % 64) same
  rw [offset state stateAligned a, offset message messageAligned b] at residue
  have index : a = b := Fin.ext (by omega)
  subst b
  exact distinct ((BitVec.add_left_inj (BitVec.ofNat 32 (4 * a.val))).mp same)

private theorem port_code [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.Proofs.BoundaryInputs data initial cells)
    {row : Delegation.Row p} (member : row ∈ data.rows) (family : row.family = .blakeG)
    (index : Fin 6) :
    (wordPort index).address.code row.assignment =
      (Cell.ram (importedConstraintsIndirectPorts[index].address row.assignment)).addressCode := by
  have present : wordPort index ∈ row.ports := by
    rw [Delegation.Row.ports, family]
    exact Array.getElem_mem (wordIndex index).isLt
  have step : (readToken row.assignment (wordPort index), row.writeToken (wordPort index)) ∈ data.steps := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, List.mem_map.mpr ⟨_, ?_, rfl⟩⟩
    simpa only [Array.mem_toList_iff] using present
  obtain ⟨cell, _, code⟩ := initialized_cell hp accepted inputs step
  change cell.addressCode = (wordPort index).address.code row.assignment at code
  rw [word_port_address] at code
  rw [indirect_cell code] at code
  simpa only [word_port_address] using code.symm

theorem call_block_domain [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced) :
    ∃ statePointer messagePointer : BitVec 32,
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧
      statePointer.toNat % 64 = 0 ∧ messagePointer.toNat % 64 = 0 ∧
      statePointer ≠ messagePointer ∧
      ∀ block : Bool, ∀ word : Fin 16,
        Cell.ram ((if block then statePointer else messagePointer) + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, tracked⟩ :=
    call_block_cells hp inverse accepted inputs
  obtain ⟨state, message, stateRead', messageRead', pointers, _, _⟩ :=
    call_pointers clockBound accepted inputs
  have stateSame := (EStateM.Result.ok.inj (stateRead.symm.trans stateRead')).1
  have messageSame := (EStateM.Result.ok.inj (messageRead.symm.trans messageRead')).1
  subst state
  subst message
  obtain ⟨ordered, permutation, _, controls, _⟩ := ordered_controls clockBound accepted inputs
  have firstBound : 0 < ordered.length := by
    rw [permutation.length_eq, inputs.calls]
    cases reduced <;> decide
  let row := ordered[0]'firstBound
  have member : row ∈ data.rows := permutation.mem_iff.mp (List.getElem_mem _)
  have family := inputs.family row member
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints (setupTable Control.controllerRows)) := by
    have h := accepted.constraints row member
    simp only [Delegation.Row.constraints, family, inputs.tables, Delegation.modeledSetup] at h
    exact Verification.holds_of_sublist h (List.sublist_append_left _ importedConstraintsTimestampLookups)
  have alignment := pointer_alignment (by omega) inverse core
  have pointer := pointers row member
  have stateLow := congrArg Word.lo pointer.1
  have messageLow := congrArg Word.lo pointer.2
  simp [Native.statePointer, Delegation.Row.readWord, Delegation.Row.ports, readToken,
    MemoryToken.word, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, Word.ofBitVec, limbBase] at stateLow
  simp [Native.messagePointer, Delegation.Row.readWord, Delegation.Row.ports, readToken,
    MemoryToken.word, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate,
    importedConstraintsMemoryPorts, Word.ofBitVec, limbBase] at messageLow
  have stateAligned : statePointer.toNat % 64 = 0 := by
    rw [stateLow, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 65536)] at alignment
    exact alignment.1
  have messageAligned : messagePointer.toNat % 64 = 0 := by
    rw [messageLow, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 65536)] at alignment
    exact alignment.2
  have operation : Delegation.Proofs.BoundaryOperationInputs data initial cells Keccak.Controller.rows := by
    refine ⟨inputs.memory, inputs.tables, ?_, ?_⟩
    all_goals intro row member other; have := inputs.family row member; simp_all
  have bounds := operation_word_bounds_at_boundary hp inverse accepted operation
  have native : row = ⟨.blakeG, row.assignment⟩ := by
    have same : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [family] using same
  have control : (row.assignment Variables.controlReadLo).val = (controlAt reduced 0).lo := by
    have value := congrArg Word.lo (controls 0 firstBound).1
    simpa [row, readToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.readCode, WordColumns.code, pairCode, Variables.controlReadLo] using value
  have controlBound : (row.assignment Variables.controlReadLo).val < 256 := by
    rw [control]
    cases reduced <;> decide
  have addresses := native_addresses (by omega) inverse core (inputs.active row member) controlBound
    (by simpa only [← native] using bounds.reads row member)
  have mapped : addressInput row.assignment controlBound =
      ⟨scheduledController reduced 0 (by cases reduced <;> decide),
        Word.ofBitVec statePointer, Word.ofBitVec messagePointer⟩ := by
    dsimp only [addressInput]
    rw [pointer.1, pointer.2]
    congr 2
    exact Fin.ext control
  rw [mapped] at addresses
  have stateAddress := congrArg (fun values : Vector (BitVec 32) 6 => values[0]) addresses
  have messageAddress := congrArg (fun values : Vector (BitVec 32) 6 => values[4]) addresses
  have stateNative : importedConstraintsIndirectPorts[0].address row.assignment = statePointer := by
    cases reduced <;> simpa [Addresses.expected, scheduledController, controllerAt, controlAt,
      Control.step, Control.stateLanes, Control.messageSchedule, Control.controllerRows, Word.ofBitVec_roundtrip] using stateAddress
  have messageNative : importedConstraintsIndirectPorts[4].address row.assignment = messagePointer := by
    cases reduced <;> simpa [Addresses.expected, scheduledController, controllerAt, controlAt,
      Control.step, Control.stateLanes, Control.messageSchedule, Control.controllerRows, Word.ofBitVec_roundtrip] using messageAddress
  have separate : statePointer ≠ messagePointer := by
    intro same
    have one := port_code clockBound accepted inputs.memory member family 0
    have six := port_code clockBound accepted inputs.memory member family 4
    change (wordPort 0).address.code row.assignment =
      (Cell.ram (importedConstraintsIndirectPorts[0].address row.assignment)).addressCode at one
    change (wordPort 4).address.code row.assignment =
      (Cell.ram (importedConstraintsIndirectPorts[4].address row.assignment)).addressCode at six
    rw [stateNative] at one
    rw [messageNative, ← same] at six
    have equal := one.trans six.symm
    have unique := row_addresses_distinct clockBound accepted inputs.memory member
    have samePorts : (row.memorySteps.map fun edge => edge.1.address)[1]'(by
        simp [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts]) =
      (row.memorySteps.map fun edge => edge.1.address)[6]'(by
        simp [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts]) := by
      simpa [Delegation.Row.memorySteps, Delegation.Row.ports, family, importedConstraintsMemoryPorts,
        wordPort, wordIndex, readToken] using equal
    have impossible := unique.getElem_inj_iff.mp samePorts
    omega
  exact ⟨statePointer, messagePointer, stateRead, messageRead, stateAligned, messageAligned, separate, tracked⟩

end Airbender.Blake2G.Proofs
