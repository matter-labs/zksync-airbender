import Slop.Blake2G.PhysicalPorts
import Slop.Delegation.Operations
import Slop.Blake2G.ControlPool

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
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

end Airbender.Blake2G.Proofs
