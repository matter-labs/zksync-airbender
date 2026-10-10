import Airbender.Review.Blake2Round.Memory
import Airbender.Review.Delegation.Operations
import Airbender.Review.Delegation.Execution

namespace Airbender.Blake2Round.Native

/-- Observe controller/pointers, chaining state, extended state and message from
    the imported native read ports. The declared round identifies the caller's
    exclusive mask; the other mode bits are observed from the circuit. These
    definitions supply neither a read value nor an expected round result. -/
def input (round : Fin 10) (w : Nat → ZMod p) : Row.Input :=
  let native : Delegation.Row p := ⟨.blakeRound, w⟩
  ⟨native.readWord (42 : Fin 43), round, decide (w Variables.controlBits[0] = 1),
    decide (w Variables.controlBits[2] = 1), decide (w Variables.controlBits[1] = 1),
    native.readWord (0 : Fin 43), native.readWord (25 : Fin 43),
    Vector.ofFn (fun i : Fin 8 => native.readWord ⟨1 + i.val, by change 1 + i.val < 43; omega⟩),
    Vector.ofFn (fun i : Fin 16 => native.readWord ⟨9 + i.val, by change 9 + i.val < 43; omega⟩),
    Vector.ofFn (fun i : Fin 16 => native.readWord ⟨26 + i.val, by change 26 + i.val < 43; omega⟩)⟩

/-- Observe the actual controller/state writes and all forty indirect addresses.
    The output property reuses the existing preparation, Clean round, chaining
    and address references in `Row.spec`. -/
def output (w : Nat → ZMod p) : Row.Output :=
  let native : Delegation.Row p := ⟨.blakeRound, w⟩
  ⟨native.writtenWord (42 : Fin 43),
    Vector.ofFn (fun i : Fin 8 => native.writtenWord ⟨1 + i.val, by change 1 + i.val < 43; omega⟩),
    Vector.ofFn (fun i : Fin 16 => native.writtenWord ⟨9 + i.val, by change 9 + i.val < 43; omega⟩),
    importedConstraintsIndirectPorts.map fun port => port.address w⟩

end Airbender.Blake2Round.Native
