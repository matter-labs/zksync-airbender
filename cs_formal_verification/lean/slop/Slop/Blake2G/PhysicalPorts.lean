import Slop.Blake2G.Addresses
import Human.Circuits.Blake2G.Execution
import Slop.Delegation.NativeViews

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def wordIndex (index : Fin 6) : Fin 9 :=
  if index.val < 4 then ⟨1 + index.val, by omega⟩ else ⟨2 + index.val, by omega⟩

def wordPort (index : Fin 6) : MemoryPort :=
  importedConstraintsMemoryPorts[wordIndex index]

theorem word_port_address (index : Fin 6) :
    (wordPort index).address = .indirect importedConstraintsIndirectPorts[index] := by
  fin_cases index <;> rfl

def addressInput (w : Nat → ZMod p) (controlBound : (w Variables.controlReadLo).val < 256) : Addresses.Input :=
  ⟨⟨⟨(w Variables.controlReadLo).val, controlBound⟩, true⟩,
    Native.statePointer w, Native.messagePointer w⟩

theorem native_addresses [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w Variables.execute = 1)
    (controlBound : (w Variables.controlReadLo).val < 256)
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded) :
    Addresses.spec (addressInput w controlBound)
      (importedConstraintsIndirectPorts.map (fun port => port.address w)) := by
  apply Addresses.Proofs.soundness hp inverse (addressInput w controlBound) _ w
  refine ⟨⟨?_, ?_⟩, holds, ⟨rfl, active, ?_, ?_, rfl⟩⟩
  · exact reads importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 9; decide))
  · exact reads importedConstraintsMemoryPorts[5] (Array.getElem_mem (by change 5 < 9; decide))
  all_goals simp [addressInput, Native.statePointer, Native.messagePointer,
    Delegation.Row.readWord, Delegation.Row.ports, readToken, MemoryToken.word,
    MemoryPort.readCode, WordColumns.code, importedConstraintsMemoryPorts]

theorem native_word_observations {p : Nat} {w : Nat → ZMod p} {before after : State}
    {controlBound : (w Variables.controlReadLo).val < 256}
    (addresses : Addresses.spec (addressInput w controlBound)
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (reads : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeG, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after) (index : Fin 6) :
    let address := (Addresses.expected (addressInput w controlBound))[index]
    ramWord before address = ((⟨.blakeG, w⟩ : Delegation.Row p).readWord (wordIndex index)).value ∧
      ramWord after address = ((⟨.blakeG, w⟩ : Delegation.Row p).writtenWord (wordIndex index)).value := by
  have member : wordPort index ∈ (⟨.blakeG, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (wordIndex index).isLt
  have result := indirect_word_observations (word_port_address index)
    (reads _ member) (writes _ member) (observed _ member)
  have address := congrArg (fun values : Vector (BitVec 32) 6 => values[index]) addresses
  simp only [Fin.getElem_fin, Vector.getElem_map] at address
  change importedConstraintsIndirectPorts[index].address w =
    (Addresses.expected (addressInput w controlBound))[index] at address
  change ramWord before (importedConstraintsIndirectPorts[index].address w) =
    ((⟨.blakeG, w⟩ : Delegation.Row p).readWord (wordIndex index)).value ∧
    ramWord after (importedConstraintsIndirectPorts[index].address w) =
    ((⟨.blakeG, w⟩ : Delegation.Row p).writtenWord (wordIndex index)).value at result
  rw [address] at result
  exact result

end Airbender.Blake2G.Proofs
