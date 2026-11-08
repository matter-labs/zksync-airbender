import Slop.Blake2G.Addresses
import Human.Circuits.Blake2G.Execution
import Slop.Delegation.NativeViews

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
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

theorem native_addresses [Fact p.Prime] (hp : 33554432 ≤ p)
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

end Airbender.Blake2G.Proofs
