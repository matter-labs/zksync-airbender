import Airbender.Review.Circuits.Blake2Round.Call
import Airbender.Proofs.Blake2Round.NativeExecution
import Airbender.Proofs.Delegation.NativeViews
import Airbender.Proofs.Trace.AtomicWrites

namespace Airbender.Blake2Round.Call.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

def indirectIndex (i : Fin 40) : Fin 43 :=
  ⟨if i.val < 24 then i.val + 1 else i.val + 2, by split <;> omega⟩

theorem cell_indirect (input : Row.Input) (i : Fin 40) :
    (cells input)[indirectIndex i] = .ram (Addresses.expected ⟨input.statePointer, input.messagePointer⟩)[i] := by
  fin_cases i <;> simp [cells, indirectIndex, Addresses.expected, Fin.getElem_fin]

theorem indirect_shape (i : Fin 40) :
    importedConstraintsMemoryPorts[(indirectIndex i).val].address =
      .indirect importedConstraintsIndirectPorts[i] := by
  fin_cases i <;> decide +kernel

theorem cells_projection {w : Nat → ZMod p} {input : Row.Input}
    (addresses : importedConstraintsIndirectPorts.map (fun port => port.address w) =
      Addresses.expected ⟨input.statePointer, input.messagePointer⟩)
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w) :
    ∀ i : Fin 43, (cells input)[i].addressCode = importedConstraintsMemoryPorts[i].address.code w := by
  have indirect (i : Fin 40) : (cells input)[indirectIndex i].addressCode =
      importedConstraintsMemoryPorts[(indirectIndex i).val].address.code w := by
    obtain ⟨cell, code⟩ := observed _ (Array.getElem_mem (indirectIndex i).isLt)
    have shape := congrArg (fun address : MemoryAddress => address.code w) (indirect_shape i)
    have original := code.trans shape
    have same := Delegation.Proofs.indirect_cell original
    have address := congrArg (fun vector : Vector (BitVec 32) 40 => vector[i]) addresses
    have address : importedConstraintsIndirectPorts[i].address w =
        (Addresses.expected ⟨input.statePointer, input.messagePointer⟩)[i] := by
      simpa only [Fin.getElem_fin, Vector.getElem_map] using address
    rw [same, address] at original
    rw [cell_indirect]
    exact original.trans shape.symm
  intro i
  by_cases zero : i.val = 0
  · have same : i = 0 := Fin.ext zero
    subst i
    simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  by_cases middle : i.val = 25
  · have same : i = 25 := Fin.ext middle
    subst i
    simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  by_cases last : i.val = 42
  · have same : i = 42 := Fin.ext last
    subst i
    simp [cells, Fin.getElem_fin, Cell.addressCode, MemoryAddress.code, importedConstraintsMemoryPorts]
  let j : Fin 40 := ⟨if i.val < 25 then i.val - 1 else i.val - 2, by split <;> omega⟩
  have same : indirectIndex j = i := by
    apply Fin.ext
    simp only [indirectIndex, j]
    split_ifs <;> omega
  simpa only [same, Fin.getElem_fin] using indirect j

theorem operands_projection (round : Fin 10) (w : Nat → ZMod p) (i : Fin 43) :
    (reads (Native.input round w))[i] = (readToken w importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  all_goals simp [reads, values, stateWord, Fin.getElem_fin, Native.input,
    Delegation.Row.readWord, Delegation.Row.ports]

theorem results_projection (round : Fin 10) (w : Nat → ZMod p) (i : Fin 43) :
    (results (Native.input round w) (Native.output w))[i] =
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec := by
  fin_cases i
  all_goals simp [results, values, stateWord, Fin.getElem_fin, Native.input, Native.output,
    Delegation.Row.readWord, Delegation.Row.writtenWord, Delegation.Row.ports,
    Delegation.Row.writeToken, readToken, MemoryToken.word, MemoryPort.readCode, MemoryPort.writeCode,
    WordColumns.code, importedConstraintsMemoryPorts]

theorem write_projection {w : Nat → ZMod p} {round : Fin 10}
    (codes : ∀ i : Fin 43, (cells (Native.input round w))[i].addressCode =
      importedConstraintsMemoryPorts[i].address.code w) :
    ((⟨.blakeRound, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
      (edge.1.address, edge.2.word.toBitVec)) =
      ((writes (Native.input round w) (Native.output w)).map fun entry => (entry.1.addressCode, entry.2)) := by
  have native : (⟨.blakeRound, w⟩ : Delegation.Row p).memorySteps =
      List.ofFn (fun i : Fin 43 => (readToken w importedConstraintsMemoryPorts[i],
        (⟨.blakeRound, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i])) := by rfl
  rw [native, List.map_ofFn]
  have expected : writes (Native.input round w) (Native.output w) =
      List.ofFn (fun i : Fin 43 => ((cells (Native.input round w))[i],
        (results (Native.input round w) (Native.output w))[i])) := by
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
    ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken importedConstraintsMemoryPorts[i]).word.toBitVec) =
      ((cells (Native.input round w))[i].addressCode, (results (Native.input round w) (Native.output w))[i])
  exact congrArg₂ Prod.mk (codes i).symm (results_projection round w i).symm

theorem executes [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p} {round : Fin 10} {before after : State}
    {domain : List Cell} {events : List MemoryAccess}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (mask : Memory.RoundMask w round) (abi : ABI (Native.input round w))
    (bounds : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded ∧
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (history : SailHistory domain events before after)
    (permutation : events.Perm ((⟨.blakeRound, w⟩ : Delegation.Row p).memorySteps.map transferEvent))
    (observed : ∀ port ∈ importedConstraintsMemoryPorts, ∃ cell : Cell,
      cell.addressCode = port.address.code w ∧
        cell.read before = .ok (readToken w port).word.toBitVec before) : Executes before after := by
  have effect := Native.Proofs.native_effects hp inverse round core mask (fun port present => (bounds port present).1)
  have codes := cells_projection effect.2.2.2 (fun port present => by
    obtain ⟨cell, code, _⟩ := observed port present
    exact ⟨cell, code⟩)
  have reads (i : Fin 43) : (cells (Native.input round w))[i].read before =
      .ok (Call.reads (Native.input round w))[i] before := by
    obtain ⟨cell, code, read⟩ := observed _ (Array.getElem_mem i.isLt)
    have same := cell_address_injective (code.trans (codes i).symm)
    rw [same] at read
    exact read.trans (congrArg (fun value => EStateM.Result.ok value before)
      (operands_projection round w i).symm)
  refine ⟨Native.input round w, Native.output w, abi, ?_, ?_, reads, effect, ?_⟩
  · refine ⟨(bounds _ (Array.getElem_mem (by change 42 < 43; decide))).1,
      (bounds _ (Array.getElem_mem (by change 0 < 43; decide))).1,
      (bounds _ (Array.getElem_mem (by change 25 < 43; decide))).1, ?_, ?_, ?_⟩
    · intro i
      simp only [Native.input, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (bounds _ (Array.getElem_mem (by change 1 + i.val < 43; omega))).1
    · intro i
      simp only [Native.input, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (bounds _ (Array.getElem_mem (by change 9 + i.val < 43; omega))).1
    · intro i
      simp only [Native.input, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (bounds _ (Array.getElem_mem (by change 26 + i.val < 43; omega))).1
  · refine ⟨(bounds _ (Array.getElem_mem (by change 42 < 43; decide))).2, ?_, ?_⟩
    · intro i
      simp only [Native.output, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (bounds _ (Array.getElem_mem (by change 1 + i.val < 43; omega))).2
    · intro i
      simp only [Native.output, Fin.getElem_fin, Vector.getElem_ofFn]
      exact (bounds _ (Array.getElem_mem (by change 9 + i.val < 43; omega))).2
  · apply atomic_writes_of_history history
    have projection := permutation.map (fun event => (event.2.1, memoryWord event.2.2.2))
    change (events.map fun event => (event.2.1, memoryWord event.2.2.2)).Perm
      ((⟨.blakeRound, w⟩ : Delegation.Row p).memorySteps.map fun edge =>
        (edge.1.address, edge.2.word.toBitVec)) at projection
    rw [write_projection codes] at projection
    exact projection

end Airbender.Blake2Round.Call.Proofs
