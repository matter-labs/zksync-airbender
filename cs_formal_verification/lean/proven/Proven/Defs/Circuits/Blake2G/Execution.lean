module
public import Human.Circuits.Blake2G.Model
public import Human.Helpers.Delegation.Operations
public import Human.Helpers.Delegation.WorkerContext
public import Human.Circuits.Blake2G.Execution

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2G/Execution.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2G.Native
open Trace
/-- The readonly state-block pointer in the imported x10 port. -/
def statePointer (w : Nat → ZMod p) : Arithmetic.Word :=
  (⟨.blakeG, w⟩ : Delegation.Row p).readWord (0 : Fin 9)
/-- The readonly message-block pointer in the imported x11 port. -/
def messagePointer (w : Nat → ZMod p) : Arithmetic.Word :=
  (⟨.blakeG, w⟩ : Delegation.Row p).readWord (5 : Fin 9)
end Airbender.Blake2G.Native
