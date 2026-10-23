import Airbender.Proofs.Blake2G.PhysicalPorts
import Airbender.Proofs.Blake2G.CallHistory
import Airbender.Proofs.Blake2G.PointerHistory
import Airbender.Proofs.Delegation.Operations

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

abbrev scheduledController (reduced : Bool) (i : Nat) (_bound : i < callCount reduced) : Control.Input :=
  controllerAt reduced i

private theorem first_round_coverage (reduced block : Bool) (word : Fin 16) :
    ∃ call : Fin 8, ∃ port : Fin 6,
      if block then port.val < 4 ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).stateOffsets[Fin.ofNat 4 port.val] = word.val
      else 4 ≤ port.val ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).messageOffsets[Fin.ofNat 2 (port.val - 4)] = word.val := by
  have finite : ∀ reduced block : Bool, ∀ word : Fin 16, ∃ call : Fin 8, ∃ port : Fin 6,
      if block then port.val < 4 ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).stateOffsets[Fin.ofNat 4 port.val] = word.val
      else 4 ≤ port.val ∧
        (Control.step (scheduledController reduced call.val (by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega))).messageOffsets[Fin.ofNat 2 (port.val - 4)] = word.val := by decide +kernel
  exact finite reduced block word

theorem call_block_cells [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced) :
    ∃ statePointer messagePointer : BitVec 32,
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧
      ∀ block : Bool, ∀ word : Fin 16,
        Cell.ram ((if block then statePointer else messagePointer) + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, pointers, _, _⟩ :=
    call_pointers clockBound accepted inputs
  obtain ⟨ordered, permutation, _, controls, _⟩ := ordered_controls clockBound accepted inputs
  have operation : Delegation.Proofs.BoundaryOperationInputs data initial cells Keccak.Controller.rows := by
    refine ⟨inputs.memory, inputs.tables, ?_, ?_⟩
    all_goals intro row member other; have := inputs.family row member; simp_all
  have bounds := operation_word_bounds_at_boundary hp inverse accepted operation
  refine ⟨statePointer, messagePointer, stateRead, messageRead, ?_⟩
  intro block word
  obtain ⟨call, index, coverage⟩ := first_round_coverage reduced block word
  have callBound : call.val < callCount reduced := by have := call.isLt; cases reduced <;> simp only [callCount, Bool.false_eq_true, ↓reduceIte] <;> omega
  have rowBound : call.val < ordered.length := by rw [permutation.length_eq, inputs.calls]; exact callBound
  let row := ordered[call.val]'rowBound
  have member : row ∈ data.rows := permutation.mem_iff.mp (List.getElem_mem _)
  have native : row = ⟨.blakeG, row.assignment⟩ := by
    have same : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [inputs.family row member] using same
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (importedConstraints (setupTable Control.controllerRows)) := by
    have h := accepted.constraints row member
    simp only [Delegation.Row.constraints, inputs.family row member, inputs.tables, Delegation.modeledSetup] at h
    exact Verification.holds_of_sublist h (List.sublist_append_left _ importedConstraintsTimestampLookups)
  have control : (row.assignment Variables.controlReadLo).val = (controlAt reduced call.val).lo := by
    have value := congrArg Word.lo (controls call.val rowBound).1
    simpa [row, readToken, MemoryToken.word, importedConstraintsMemoryPorts,
      MemoryPort.readCode, WordColumns.code, pairCode, Variables.controlReadLo] using value
  have controlBound : (row.assignment Variables.controlReadLo).val < 256 := by
    rw [control]
    exact (scheduledController reduced call.val callBound).register.isLt
  have addresses := native_addresses (by omega) inverse core (inputs.active row member) controlBound
    (by simpa only [← native] using bounds.reads row member)
  have mapped : addressInput row.assignment controlBound =
      ⟨scheduledController reduced call.val callBound, Word.ofBitVec statePointer, Word.ofBitVec messagePointer⟩ := by
    dsimp only [addressInput]
    rw [(pointers row member).1, (pointers row member).2]
    congr 2
    exact Fin.ext control
  rw [mapped] at addresses
  have address := congrArg (fun values : Vector (BitVec 32) 6 => values[index]) addresses
  simp only [Fin.getElem_fin, Vector.getElem_map] at address
  change importedConstraintsIndirectPorts[index].address row.assignment = _ at address
  have present : wordPort index ∈ row.ports := by
    rw [Delegation.Row.ports, inputs.family row member]
    exact Array.getElem_mem (wordIndex index).isLt
  have tracked := initialized_indirect_cell_at_boundary clockBound accepted inputs.memory member present (word_port_address index)
  rw [address] at tracked
  cases block
  · simp only [Bool.false_eq_true, ↓reduceIte] at coverage ⊢
    obtain ⟨selected, offset⟩ := coverage
    fin_cases index
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Nat.reduceLT,
      Fin.getElem_fin] at selected
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Fin.getElem_fin] at offset
    all_goals simpa only [Addresses.expected, Word.ofBitVec_roundtrip, Fin.getElem_fin,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, offset] using tracked
  · simp only [↓reduceIte] at coverage ⊢
    obtain ⟨selected, offset⟩ := coverage
    fin_cases index
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Nat.reduceLT,
      Fin.getElem_fin] at selected
    all_goals norm_num only [Fin.val_ofNat, Nat.reduceSub, Fin.getElem_fin] at offset
    all_goals simpa only [Addresses.expected, Word.ofBitVec_roundtrip, Fin.getElem_fin,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, offset] using tracked

end Airbender.Blake2G.Proofs
