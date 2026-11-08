import Human.Circuits.UnifiedReduced.Control
import Human.Helpers.Decoder.Instruction
import Mathlib.Logic.Relation
import Slop.Trace.RowContext
import Slop.UnifiedReduced.Values
import Slop.UnifiedReduced.ZeroRegister
import Slop.UnifiedReduced.ControlProjection

namespace Airbender.UnifiedReduced.Control.Proofs
open Arithmetic Reference.RiscV Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem right_sign_source [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 21 + w 22 + w 23 + w 24 = 1) : w 60 = w 43 + w 23 * w 9 := by
  have gate := Verification.assertion_of_holds holds ⟨14, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at gate
  linear_combination gate

end Airbender.UnifiedReduced.Control.Proofs
