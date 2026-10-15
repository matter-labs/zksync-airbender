import Airbender.Proofs.Keccak.Call
import Airbender.Proofs.Delegation.NativeViews
import Airbender.Proofs.Trace.AtomicWrites

namespace Airbender.Keccak.Call.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

def nativeArguments (control : ControlState) (w : Nat → ZMod p) : Arguments :=
  ⟨control, statePointer w, Vector.ofFn (Native.readLane w)⟩

def indirectIndex (i : Fin 12) : Fin 14 := ⟨i.val + 2, by omega⟩

theorem cell_indirect (input : Arguments) (i : Fin 12) :
    (cells input)[indirectIndex i] = .ram (input.pointer.toBitVec + BitVec.ofNat 32
      (8 * (indices input.control)[i.val / 2]'(by omega) + 4 * (i.val % 2))) := by
  fin_cases i <;> simp [cells, indirectIndex, Fin.getElem_fin]

theorem indirect_shape (i : Fin 12) :
    importedConstraintsMemoryPorts[(indirectIndex i).val].address =
      .indirect importedConstraintsIndirectPorts[i] := by
  fin_cases i <;> decide +kernel

theorem cells_projection {w : Nat → ZMod p} {control : ControlState}
    (addresses : ∀ i : Fin 12, importedConstraintsIndirectPorts[i].address w =
      (statePointer w).toBitVec + BitVec.ofNat 32
        (8 * (indices control)[i.val / 2]'(by omega) + 4 * (i.val % 2)))
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ i : Fin 14, (cells (nativeArguments control w))[i].addressCode =
      importedConstraintsMemoryPorts[i].address.code w := by
  have indirect (i : Fin 12) : (cells (nativeArguments control w))[indirectIndex i].addressCode =
      importedConstraintsMemoryPorts[(indirectIndex i).val].address.code w := by
    obtain ⟨cell, code⟩ := observed _ (Array.getElem_mem (indirectIndex i).isLt)
    have shape := congrArg (fun address : MemoryAddress => address.code w) (indirect_shape i)
    have original := code.trans shape
    have same := Delegation.Proofs.indirect_cell original
    rw [same, addresses i] at original
    rw [cell_indirect]
    exact original.trans shape.symm
  intro i
  by_cases zero : i.val = 0
  · have same : i = 0 := Fin.ext zero
    subst i
    simp [cells, nativeArguments, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  by_cases pointer : i.val = 1
  · have same : i = 1 := Fin.ext pointer
    subst i
    simp [cells, nativeArguments, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  let j : Fin 12 := ⟨i.val - 2, by omega⟩
  have same : indirectIndex j = i := by apply Fin.ext; simp only [indirectIndex, j]; omega
  simpa only [same, Fin.getElem_fin] using indirect j

theorem controller_words (w : Nat → ZMod p) :
    (readToken w importedConstraintsMemoryPorts[0]).word = ⟨(w 3).val, (w 4).val⟩ ∧
    ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[0]).word =
      ⟨(w 5).val, (w 6).val⟩ := by
  simp [readToken, MemoryPort.readCode, Delegation.Row.writeToken, MemoryPort.writeCode,
    MemoryToken.word, WordColumns.code, importedConstraintsMemoryPorts]

theorem pointer_words (w : Nat → ZMod p) :
    (readToken w importedConstraintsMemoryPorts[1]).word = statePointer w ∧
    ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[1]).word = statePointer w := by
  simp [statePointer, readToken, MemoryPort.readCode, Delegation.Row.writeToken, MemoryPort.writeCode,
    MemoryToken.word, WordColumns.code, importedConstraintsMemoryPorts]

theorem read_halves {w : Nat → ZMod p}
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) (lane : Fin 6) :
    half (Native.readLane w lane) false =
        (readToken w (importedConstraintsMemoryPorts[2 + 2 * lane.val]'(by change _ < 14; omega))).word.toBitVec ∧
    half (Native.readLane w lane) true =
        (readToken w (importedConstraintsMemoryPorts[3 + 2 * lane.val]'(by change _ < 14; omega))).word.toBitVec := by
  constructor
  · exact low_half _ _
  · exact high_half (bounds _ (Array.getElem_mem (by change 2 + 2 * lane.val < 14; omega)))

theorem written_halves {w : Nat → ZMod p}
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded) (lane : Fin 6) :
    half (Native.writtenLane w lane) false =
        ((⟨.keccak, w⟩ : Delegation.Row p).writeToken
          (importedConstraintsMemoryPorts[2 + 2 * lane.val]'(by change _ < 14; omega))).word.toBitVec ∧
    half (Native.writtenLane w lane) true =
        ((⟨.keccak, w⟩ : Delegation.Row p).writeToken
          (importedConstraintsMemoryPorts[3 + 2 * lane.val]'(by change _ < 14; omega))).word.toBitVec := by
  constructor
  · exact low_half _ _
  · exact high_half (bounds _ (Array.getElem_mem (by change 2 + 2 * lane.val < 14; omega)))

theorem controller_write [Fact p.Prime] (hp : 4096 ≤ p)
    {w : Nat → ZMod p} {control : ControlState}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Controller.rows))) (active : w 0 = 1)
    (binding : (readToken w importedConstraintsMemoryPorts[0]).word = ⟨control.packed, 0⟩) :
    ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[0]).word =
      ⟨control.nextPacked, 0⟩ := by
  have lo := congrArg Word.lo ((controller_words w).1.symm.trans binding)
  have next := Keccak.Proofs.next_control (p := p) (setup := setupTable Controller.rows) (w := w)
    hp control core active lo
  have high := Keccak.Proofs.control_high_zero (p := p) (setup := setupTable Controller.rows) (w := w) core
  rw [(controller_words w).2, next, high.2, ZMod.val_zero]

theorem addresses_of_effects [Fact p.Prime] (hp : 4096 ≤ p)
    {w : Nat → ZMod p} {control : ControlState}
    (effects : Native.RowEffects w) (active : w 0 = 1) (read : (w 3).val = control.packed) :
    ∀ i : Fin 12, importedConstraintsIndirectPorts[i].address w =
      (statePointer w).toBitVec + BitVec.ofNat 32
        (8 * (indices control)[i.val / 2]'(by omega) + 4 * (i.val % 2)) := by
  obtain ⟨nativeKey, keyValue, output⟩ := effects.indices
  have one : (w 0).val = 1 := by rw [active]; exact ZMod.val_one'' (by omega : p ≠ 1)
  have same : nativeKey = key control := by
    apply Fin.ext
    change nativeKey.val = control.packed + 2048
    rw [keyValue, read, one]
  have selected (lane : Fin 6) : (w (7 + lane.val)).val = (indices control)[lane.val] := by
    have result := output lane
    rw [same] at result
    simpa only [indices, Fin.getElem_fin] using result
  intro i
  have address := effects.addresses.addresses i
  rw [selected ⟨i.val / 2, by omega⟩] at address
  exact address

theorem operands_projection {w : Nat → ZMod p} {control : ControlState}
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded)
    (binding : (readToken w importedConstraintsMemoryPorts[0]).word = ⟨control.packed, 0⟩)
    (i : Fin 14) :
    (reads (nativeArguments control w))[i] = (readToken w importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  · simpa [reads, values, nativeArguments, Fin.getElem_fin, Word.toBitVec, Word.value] using
      (congrArg Word.toBitVec binding).symm
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using
      (congrArg Word.toBitVec (pointer_words w).1).symm
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 0).1
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 0).2
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 1).1
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 1).2
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 2).1
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 2).2
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 3).1
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 3).2
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 4).1
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 4).2
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 5).1
  · simpa [reads, values, nativeArguments, Fin.getElem_fin] using (read_halves bounds 5).2

theorem results_projection {w : Nat → ZMod p} {control : ControlState}
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (binding : ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[0]).word =
      ⟨control.nextPacked, 0⟩) (i : Fin 14) :
    (results (nativeArguments control w) (Native.writtenLanes w))[i] =
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  · simpa [results, values, nativeArguments, Fin.getElem_fin, Word.toBitVec, Word.value] using
      (congrArg Word.toBitVec binding).symm
  · simpa [results, values, nativeArguments, Fin.getElem_fin] using
      (congrArg Word.toBitVec (pointer_words w).2).symm
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 0).1
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 0).2
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 1).1
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 1).2
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 2).1
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 2).2
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 3).1
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 3).2
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 4).1
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 4).2
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 5).1
  · simpa [results, values, nativeArguments, Native.writtenLanes, Fin.getElem_fin] using (written_halves bounds 5).2

theorem read_lane_bound {w : Nat → ZMod p}
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) (lane : Fin 6) :
    Native.readLane w lane < 2 ^ 64 :=
  lane_bound (bounds _ (Array.getElem_mem (by change 2 + 2 * lane.val < 14; omega)))
    (bounds _ (Array.getElem_mem (by change 3 + 2 * lane.val < 14; omega)))

theorem written_lane_bound {w : Nat → ZMod p}
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded) (lane : Fin 6) :
    Native.writtenLane w lane < 2 ^ 64 :=
  lane_bound (bounds _ (Array.getElem_mem (by change 2 + 2 * lane.val < 14; omega)))
    (bounds _ (Array.getElem_mem (by change 3 + 2 * lane.val < 14; omega)))

theorem write_projection {w : Nat → ZMod p} {control : ControlState}
    (codes : ∀ i : Fin 14, (cells (nativeArguments control w))[i].addressCode =
      importedConstraintsMemoryPorts[i].address.code w)
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (binding : ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[0]).word =
      ⟨control.nextPacked, 0⟩) :
    ((⟨.keccak, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
      (edge.1.address, edge.2.word.toBitVec)) =
      ((writes (nativeArguments control w) (Native.writtenLanes w)).map fun entry => (entry.1.addressCode, entry.2)) := by
  have native : (⟨.keccak, w⟩ : Delegation.Row p).memorySteps =
      List.ofFn (fun i : Fin 14 => (readToken w importedConstraintsMemoryPorts[i],
        (⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i])) := by rfl
  rw [native, List.map_ofFn]
  have expected : writes (nativeArguments control w) (Native.writtenLanes w) =
      List.ofFn (fun i : Fin 14 => ((cells (nativeArguments control w))[i],
        (results (nativeArguments control w) (Native.writtenLanes w))[i])) := by
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
    ((⟨.keccak, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec) =
      ((cells (nativeArguments control w))[i].addressCode,
        (results (nativeArguments control w) (Native.writtenLanes w))[i])
  exact congrArg₂ Prod.mk (codes i).symm (results_projection bounds binding i).symm

theorem executes [Fact p.Prime] (hp : 16777216 ≤ p) (inverse : 256 * (-7864320 : ZMod p) = 1)
    {w : Nat → ZMod p} {control : ControlState} {before after : State}
    {domain : List Cell} {events : List MemoryAccess}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Controller.rows)))
    (active : w 0 = 1) (abi : ABI (nativeArguments control w))
    (binding : (readToken w importedConstraintsMemoryPorts[0]).word = ⟨control.packed, 0⟩)
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded ∧
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (history : SailHistory domain events before after)
    (permutation : events.Perm ((⟨.keccak, w⟩ : Delegation.Row p).memorySteps.map transferEvent))
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) : Executes before after := by
  have low := congrArg Word.lo ((controller_words w).1.symm.trans binding)
  have readsBound := fun port present => (bounds port present).1
  have writesBound := fun port present => (bounds port present).2
  have effects := Native.Proofs.native_effects hp inverse core active readsBound
  have addresses := addresses_of_effects (by omega) effects active low
  have codes := cells_projection addresses (fun port present => by
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩)
  have written := controller_write (by omega) core active binding
  have reads (i : Fin 14) : (cells (nativeArguments control w))[i].read before =
      .ok (Call.reads (nativeArguments control w))[i] before := by
    obtain ⟨cell, code, read⟩ := observed _ (Array.getElem_mem i.isLt)
    have same := cell_address_injective (code.trans (codes i).symm)
    rw [same] at read
    exact read.trans (congrArg (fun value => EStateM.Result.ok value before)
      (operands_projection readsBound binding i).symm)
  refine ⟨nativeArguments control w, Native.writtenLanes w, abi, ?_, reads,
    native_operation effects low abi.control, ?_⟩
  · intro i
    simpa only [Native.writtenLanes, Fin.getElem_fin, Vector.getElem_ofFn] using written_lane_bound writesBound i
  · apply atomic_writes_of_history history
    have projection := permutation.map (fun event => (event.2.1, memoryWord event.2.2.2))
    change (events.map fun event => (event.2.1, memoryWord event.2.2.2)).Perm
      ((⟨.keccak, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
        (edge.1.address, edge.2.word.toBitVec)) at projection
    rw [write_projection codes writesBound written] at projection
    exact projection

end Airbender.Keccak.Call.Proofs
