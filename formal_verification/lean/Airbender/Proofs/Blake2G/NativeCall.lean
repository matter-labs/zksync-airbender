import Airbender.Review.Circuits.Blake2G.Call
import Airbender.Proofs.Blake2G.NativeEffects
import Airbender.Proofs.Blake2G.Addresses
import Airbender.Proofs.Delegation.NativeViews
import Airbender.Proofs.Trace.AtomicWrites

namespace Airbender.Blake2G.Call.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

def nativeArguments (register : Fin 256) (w : Nat → ZMod p) : Arguments :=
  ⟨⟨⟨register, true⟩, Native.statePointer w, Native.messagePointer w⟩, Native.input w⟩

def indirectIndex (i : Fin 6) : Fin 9 :=
  ⟨if i.val < 4 then i.val + 1 else i.val + 2, by split <;> omega⟩

theorem cell_indirect (input : Addresses.Input) (i : Fin 6) :
    (cells input)[indirectIndex i] = .ram (Addresses.expected input)[i] := by
  fin_cases i <;> simp [cells, indirectIndex, Fin.getElem_fin]

theorem indirect_shape (i : Fin 6) :
    importedConstraintsMemoryPorts[(indirectIndex i).val].address =
      .indirect importedConstraintsIndirectPorts[i] := by
  fin_cases i <;> decide +kernel

theorem cells_projection {w : Nat → ZMod p} {input : Addresses.Input}
    (addresses : importedConstraintsIndirectPorts.map (fun port => port.address w) = Addresses.expected input)
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ i : Fin 9, (cells input)[i].addressCode = importedConstraintsMemoryPorts[i].address.code w := by
  have indirect (i : Fin 6) : (cells input)[indirectIndex i].addressCode =
      importedConstraintsMemoryPorts[(indirectIndex i).val].address.code w := by
    obtain ⟨cell, code⟩ := observed _ (Array.getElem_mem (indirectIndex i).isLt)
    have shape := congrArg (fun address : MemoryAddress => address.code w) (indirect_shape i)
    have original := code.trans shape
    have same := Delegation.Proofs.indirect_cell original
    have address := congrArg (fun vector : Vector (BitVec 32) 6 => vector[i]) addresses
    have address : importedConstraintsIndirectPorts[i].address w = (Addresses.expected input)[i] := by
      simpa only [Fin.getElem_fin, Vector.getElem_map] using address
    rw [same, address] at original
    rw [cell_indirect]
    exact original.trans shape.symm
  intro i
  fin_cases i
  · simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  · exact indirect 0
  · exact indirect 1
  · exact indirect 2
  · exact indirect 3
  · simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  · exact indirect 4
  · exact indirect 5
  · simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]

theorem operands_projection {w : Nat → ZMod p} {register : Fin 256}
    (control : (readToken w importedConstraintsMemoryPorts[8]).word = ⟨register.val, 0⟩)
    (i : Fin 9) :
    (reads (nativeArguments register w))[i] = (readToken w importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  case «8» =>
    simpa [reads, nativeArguments, Fin.getElem_fin] using (congrArg Word.toBitVec control).symm
  all_goals simp [reads, nativeArguments, Fin.getElem_fin, Native.input, Native.statePointer,
    Native.messagePointer, Delegation.Row.readWord, Delegation.Row.ports]

theorem results_projection {w : Nat → ZMod p} {register : Fin 256}
    (control : (Control.step ⟨register, true⟩).register =
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[8]).word)
    (i : Fin 9) :
    (results (nativeArguments register w) (Native.output w))[i] =
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  case «8» =>
    simpa [results, nativeArguments, Fin.getElem_fin] using congrArg Word.toBitVec control
  all_goals simp [results, nativeArguments, Fin.getElem_fin, Native.output, Native.input,
    Native.statePointer, Native.messagePointer, Delegation.Row.readWord, Delegation.Row.writtenWord,
    Delegation.Row.ports, Delegation.Row.writeToken, readToken, MemoryToken.word,
    MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code, importedConstraintsMemoryPorts]

theorem controller_words (w : Nat → ZMod p) :
    (readToken w importedConstraintsMemoryPorts[8]).word = ⟨(w 3).val, (w 4).val⟩ ∧
    ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[8]).word =
      ⟨(w 5).val, (w 6).val⟩ := by
  simp [readToken, MemoryPort.readCode, Delegation.Row.writeToken, MemoryPort.writeCode,
    MemoryToken.word, WordColumns.code, importedConstraintsMemoryPorts]

theorem controller_write [Fact p.Prime] (hp : 512 ≤ p) {w : Nat → ZMod p} {register : Fin 256}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w 0 = 1)
    (control : (readToken w importedConstraintsMemoryPorts[8]).word = ⟨register.val, 0⟩) :
    (Control.step ⟨register, true⟩).register =
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[8]).word := by
  let output : Control.Output := ⟨⟨(w 5).val, (w 6).val⟩,
    Variables.stateOffsetColumns.map (fun column => (w column).val),
    Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
  have lo := congrArg Word.lo ((controller_words w).1.symm.trans control)
  have mapping : Control.Mapping ⟨register, true⟩ output w := ⟨lo.symm, active, rfl⟩
  have checked := Control.Proofs.soundness (p := p) hp ⟨register, true⟩ output w ⟨core, mapping⟩
  exact (congrArg Control.Output.register checked).symm.trans (controller_words w).2.symm

theorem write_projection {w : Nat → ZMod p} {register : Fin 256}
    (codes : ∀ i : Fin 9, (cells (nativeArguments register w).addresses)[i].addressCode =
      importedConstraintsMemoryPorts[i].address.code w)
    (control : (Control.step ⟨register, true⟩).register =
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[8]).word) :
    ((⟨.blakeG, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
      (edge.1.address, edge.2.word.toBitVec)) =
      ((writes (nativeArguments register w) (Native.output w)).map
        fun entry => (entry.1.addressCode, entry.2)) := by
  have native : (⟨.blakeG, w⟩ : Delegation.Row p).memorySteps =
      List.ofFn (fun i : Fin 9 => (readToken w importedConstraintsMemoryPorts[i],
        (⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i])) := by rfl
  rw [native, List.map_ofFn]
  have expected : writes (nativeArguments register w) (Native.output w) =
      List.ofFn (fun i : Fin 9 => ((cells (nativeArguments register w).addresses)[i],
        (results (nativeArguments register w) (Native.output w))[i])) := by
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
    ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec) =
      ((cells (nativeArguments register w).addresses)[i].addressCode,
        (results (nativeArguments register w) (Native.output w))[i])
  exact congrArg₂ Prod.mk (codes i).symm (results_projection control i).symm

theorem executes [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p} {register : Fin 256} {before after : State}
    {domain : List Cell} {events : List MemoryAccess}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (abi : ABI (nativeArguments register w).addresses) (active : w 0 = 1)
    (control : (readToken w importedConstraintsMemoryPorts[8]).word = ⟨register.val, 0⟩)
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded ∧
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (history : SailHistory domain events before after)
    (permutation : events.Perm ((⟨.blakeG, w⟩ : Delegation.Row p).memorySteps.map transferEvent))
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) : Executes before after := by
  have lo := congrArg Word.lo ((controller_words w).1.symm.trans control)
  have pointers : (nativeArguments register w).addresses.statePointer = ⟨(w 13).val, (w 14).val⟩ ∧
      (nativeArguments register w).addresses.messagePointer = ⟨(w 31).val, (w 32).val⟩ := by
    simp [nativeArguments, Native.statePointer, Native.messagePointer, Delegation.Row.readWord,
      Delegation.Row.ports, readToken, MemoryPort.readCode, MemoryToken.word, WordColumns.code,
      importedConstraintsMemoryPorts]
  have mapping : Addresses.Mapping (nativeArguments register w).addresses
      (importedConstraintsIndirectPorts.map fun port => port.address w) w :=
    ⟨lo.symm, active, pointers.1, pointers.2, rfl⟩
  have addresses := Addresses.Proofs.soundness (p := p) (by omega) inverse
    (nativeArguments register w).addresses _ w ⟨abi.bounded, core, mapping⟩
  have codes := cells_projection addresses (fun port present => by
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩)
  have writtenControl := controller_write (p := p) (by omega) core active control
  have reads (i : Fin 9) : (cells (nativeArguments register w).addresses)[i].read before =
      .ok (Call.reads (nativeArguments register w))[i] before := by
    obtain ⟨cell, code, read⟩ := observed _ (Array.getElem_mem i.isLt)
    have same := cell_address_injective (code.trans (codes i).symm)
    rw [same] at read
    exact read.trans (congrArg (fun value => EStateM.Result.ok value before)
      (operands_projection control i).symm)
  refine ⟨nativeArguments register w, Native.output w, abi, ?_, ?_, ?_, ?_, reads,
    Native.Proofs.native_effects hp inverse core (fun port present => (bounds port present).1), ?_⟩
  · exact ⟨(bounds _ (Array.getElem_mem (by change 1 < 9; decide))).1,
      (bounds _ (Array.getElem_mem (by change 2 < 9; decide))).1,
      (bounds _ (Array.getElem_mem (by change 3 < 9; decide))).1,
      (bounds _ (Array.getElem_mem (by change 4 < 9; decide))).1⟩
  · exact (bounds _ (Array.getElem_mem (by change 6 < 9; decide))).1
  · exact (bounds _ (Array.getElem_mem (by change 7 < 9; decide))).1
  · exact ⟨(bounds _ (Array.getElem_mem (by change 1 < 9; decide))).2,
      (bounds _ (Array.getElem_mem (by change 2 < 9; decide))).2,
      (bounds _ (Array.getElem_mem (by change 3 < 9; decide))).2,
      (bounds _ (Array.getElem_mem (by change 4 < 9; decide))).2⟩
  · apply atomic_writes_of_history history
    have projection := permutation.map (fun event => (event.2.1, memoryWord event.2.2.2))
    change (events.map fun event => (event.2.1, memoryWord event.2.2.2)).Perm
      ((⟨.blakeG, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
        (edge.1.address, edge.2.word.toBitVec)) at projection
    rw [write_projection codes writtenControl] at projection
    exact projection

end Airbender.Blake2G.Call.Proofs
