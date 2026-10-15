import Airbender.Proofs.Bigint.Call
import Airbender.Proofs.Bigint.NativeExecution
import Airbender.Proofs.Bigint.Addresses
import Airbender.Proofs.Delegation.NativeViews
import Airbender.Proofs.Trace.AtomicWrites

namespace Airbender.Bigint.Call.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

def indirectIndex (i : Fin 16) : Fin 19 :=
  ⟨if i.val < 8 then i.val + 1 else i.val + 2, by split <;> omega⟩

theorem expected_address (pointers : Addresses.Input) (i : Fin 16) :
    (Addresses.expected pointers)[i] =
      if i.val < 8 then pointers.left.toBitVec + BitVec.ofNat 32 (4 * i.val)
      else pointers.right.toBitVec + BitVec.ofNat 32 (4 * (i.val - 8)) := by
  change ((Vector.ofFn fun j : Fin 8 => pointers.left.toBitVec + BitVec.ofNat 32 (4 * j.val)) +++
    (Vector.ofFn fun j : Fin 8 => pointers.right.toBitVec + BitVec.ofNat 32 (4 * j.val)))[i.val] = _
  rw [Vector.getElem_append]
  split_ifs <;> simp only [Vector.getElem_ofFn]

theorem cell_indirect (pointers : Addresses.Input) (i : Fin 16) :
    (cells pointers)[indirectIndex i] = .ram (Addresses.expected pointers)[i] := by
  rw [expected_address]
  fin_cases i <;> simp [cells, Fin.getElem_fin, indirectIndex]

theorem indirect_shape (i : Fin 16) :
    importedConstraintsMemoryPorts[(indirectIndex i).val].address =
      .indirect importedConstraintsIndirectPorts[i] := by
  fin_cases i <;> decide +kernel

theorem cells_projection {w : Nat → ZMod p} {pointers : Addresses.Input}
    (addresses : importedConstraintsIndirectPorts.map (fun port => port.address w) =
      Addresses.expected pointers)
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ i : Fin 19, (cells pointers)[i].addressCode =
      importedConstraintsMemoryPorts[i].address.code w := by
  have indirect (i : Fin 16) :
      ((cells pointers)[indirectIndex i]).addressCode =
        importedConstraintsMemoryPorts[(indirectIndex i).val].address.code w := by
    obtain ⟨cell, code⟩ := observed _ (Array.getElem_mem (indirectIndex i).isLt)
    have code := code.trans (congrArg (fun address : MemoryAddress => address.code w) (indirect_shape i))
    have equal := Delegation.Proofs.indirect_cell code
    have address := congrArg (fun vector : Vector (BitVec 32) 16 => vector[i]) addresses
    have address : importedConstraintsIndirectPorts[i].address w = (Addresses.expected pointers)[i] := by
      simpa only [Fin.getElem_fin, Vector.getElem_map] using address
    rw [equal, address] at code
    rw [cell_indirect]
    exact code.trans (congrArg (fun address : MemoryAddress => address.code w) (indirect_shape i)).symm
  intro i
  fin_cases i
  · simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code,
      importedConstraintsMemoryPorts]
  · exact indirect 0
  · exact indirect 1
  · exact indirect 2
  · exact indirect 3
  · exact indirect 4
  · exact indirect 5
  · exact indirect 6
  · exact indirect 7
  · simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code,
      importedConstraintsMemoryPorts]
  · exact indirect 8
  · exact indirect 9
  · exact indirect 10
  · exact indirect 11
  · exact indirect 12
  · exact indirect 13
  · exact indirect 14
  · exact indirect 15
  · simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code,
      importedConstraintsMemoryPorts]

theorem results_projection (w : Nat → ZMod p) (i : Fin 19) :
    (results (Addresses.nativeInput w) (Native.limbs w Variables.rightLimbs) (Native.output w))[i] =
      ((⟨.bigint, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  all_goals simp [results, Fin.getElem_fin, word, Addresses.nativeInput, Native.limbs, Native.output,
    Variables.rightLimbs, Variables.writtenLimbs,
    readToken, MemoryPort.readCode, MemoryPort.writeCode, Delegation.Row.writeToken,
    MemoryToken.word, WordColumns.code, importedConstraintsMemoryPorts]

theorem operands_projection {w : Nat → ZMod p} {command : ExternalBoundary.BigintABI.Command}
    (binding : ExternalBoundary.BigintABI.Binding w command) (i : Fin 19) :
    (operands (Addresses.nativeInput w) command (Native.limbs w Variables.leftLimbs)
      (Native.limbs w Variables.rightLimbs))[i] =
      (readToken w importedConstraintsMemoryPorts[i]).word.toBitVec := by
  have control := congrArg Word.toBitVec binding
  fin_cases i
  case «18» =>
    simpa [operands, results, Fin.getElem_fin, ExternalBoundary.BigintABI.input] using control.symm
  all_goals
    simp [operands, results, Fin.getElem_fin, word, Addresses.nativeInput, Native.limbs,
      Variables.leftLimbs, Variables.rightLimbs, readToken, MemoryPort.readCode,
      MemoryToken.word, WordColumns.code, importedConstraintsMemoryPorts]

theorem write_projection {w : Nat → ZMod p}
    (codes : ∀ i : Fin 19, (cells (Addresses.nativeInput w))[i].addressCode =
      importedConstraintsMemoryPorts[i].address.code w) :
    ((⟨.bigint, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
      (edge.1.address, edge.2.word.toBitVec)) =
      ((writes (Addresses.nativeInput w) (Native.limbs w Variables.rightLimbs) (Native.output w)).map
        fun entry => (entry.1.addressCode, entry.2)) := by
  have native : (⟨.bigint, w⟩ : Delegation.Row p).memorySteps =
      List.ofFn (fun i : Fin 19 => (readToken w importedConstraintsMemoryPorts[i],
        (⟨.bigint, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i])) := by rfl
  rw [native, List.map_ofFn]
  have expected : writes (Addresses.nativeInput w) (Native.limbs w Variables.rightLimbs) (Native.output w) =
      List.ofFn (fun i : Fin 19 => ((cells (Addresses.nativeInput w))[i],
        (results (Addresses.nativeInput w) (Native.limbs w Variables.rightLimbs) (Native.output w))[i])) := by
    unfold writes
    rw [← Vector.toList_ofFn]
    apply congrArg Vector.toList
    apply Vector.ext
    intro i bound
    simp [Fin.getElem_fin]
  rw [expected, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (importedConstraintsMemoryPorts[i].address.code w,
    ((⟨.bigint, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec) =
      ((cells (Addresses.nativeInput w))[i].addressCode,
        (results (Addresses.nativeInput w) (Native.limbs w Variables.rightLimbs) (Native.output w))[i])
  exact congrArg₂ Prod.mk (codes i).symm (results_projection w i).symm

theorem executes {w : Nat → ZMod babyBearModulus}
    {command : ExternalBoundary.BigintABI.Command} {before after : State}
    {domain : List Cell} {events : List MemoryAccess}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (abi : Addresses.PointerABI (Addresses.nativeInput w))
    (binding : ExternalBoundary.BigintABI.Binding w command)
    (history : SailHistory domain events before after)
    (permutation : events.Perm ((⟨.bigint, w⟩ : Delegation.Row babyBearModulus).memorySteps.map transferEvent))
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) : Executes before after := by
  have nativePointers : Addresses.nativeInput w = ⟨⟨(w 3).val, (w 4).val⟩, ⟨(w 37).val, (w 38).val⟩⟩ := by
    simp [Addresses.nativeInput, Trace.Proofs.read_word, importedConstraintsMemoryPorts, WordColumns.evaluate]
  have mapped : Addresses.Mapping (Addresses.nativeInput w)
      (importedConstraintsIndirectPorts.map fun port => port.address w) w :=
    ⟨by rw [nativePointers], by rw [nativePointers], rfl⟩
  have addresses := (Addresses.Proofs.soundness (by decide) (by decide)
    (Addresses.nativeInput w) _ w ⟨abi.bounded, holds, mapped⟩).2.2
  have codes := cells_projection addresses (fun port present => by
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩)
  have reads (i : Fin 19) : (cells (Addresses.nativeInput w))[i].read before =
      .ok (operands (Addresses.nativeInput w) command (Native.limbs w Variables.leftLimbs)
        (Native.limbs w Variables.rightLimbs))[i] before := by
    obtain ⟨cell, code, read⟩ := observed _ (Array.getElem_mem i.isLt)
    have same := cell_address_injective (code.trans (codes i).symm)
    rw [same] at read
    exact read.trans (congrArg (fun value => EStateM.Result.ok value before)
      (operands_projection binding i).symm)
  have bounds := Bigint.Proofs.mapped_source_ranges (by decide) holds
    (left := Native.limbs w Variables.leftLimbs) (right := Native.limbs w Variables.rightLimbs)
    (by intro i; simp [Native.limbs]) (by intro i; simp [Native.limbs])
  have selected := ExternalBoundary.BigintABI.Proofs.selected (p := babyBearModulus)
    (setup := setupTable) (w := w) (command := command) (by decide) holds binding
  have carry := incoming_carry (p := babyBearModulus) (setup := setupTable)
    (w := w) (command := command) (by decide) holds binding
  have effect := operation (w := w) (command := command)
    (Native.Proofs.arithmetic_effects holds) selected carry
  apply executes_of_footprint abi bounds reads effect
  apply atomic_writes_of_history history
  have projection := permutation.map (fun event => (event.2.1, memoryWord event.2.2.2))
  change (events.map fun event => (event.2.1, memoryWord event.2.2.2)).Perm
    ((⟨.bigint, w⟩ : Delegation.Row babyBearModulus).memorySteps.map fun edge =>
      (edge.1.address, edge.2.word.toBitVec)) at projection
  rw [write_projection codes] at projection
  exact projection

end Airbender.Bigint.Call.Proofs
