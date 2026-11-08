import Slop.Delegation.NativeViews
import Slop.Blake2Round.CallGroups

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def wordIndex (index : Fin 40) : Fin 43 :=
  if h : index.val < 24 then ⟨1 + index.val, by omega⟩ else ⟨2 + index.val, by omega⟩

private def wordPort (index : Fin 40) : MemoryPort :=
  importedConstraintsMemoryPorts[wordIndex index]

private theorem word_port_address (index : Fin 40) :
    (wordPort index).address = .indirect importedConstraintsIndirectPorts[index] := by
  fin_cases index <;> rfl

private theorem word_address {p : Nat} {w : Nat → ZMod p} {round : Fin 10}
    (addresses : Addresses.spec ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩
      (Native.output w).addresses) (index : Fin 40) :
    importedConstraintsIndirectPorts[index].address w =
      (Addresses.expected ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩)[index] := by
  have address := congrArg (fun values : Vector (BitVec 32) 40 => values[index]) addresses
  change (importedConstraintsIndirectPorts.map (fun port => port.address w))[index] = _ at address
  simpa only [Fin.getElem_fin, Vector.getElem_map] using address

end Airbender.Blake2Round.Proofs
