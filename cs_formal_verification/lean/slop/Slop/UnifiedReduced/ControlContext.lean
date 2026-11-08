module
public import Human.Circuits.JumpBranchSlt.Model
public import Mathlib.Logic.Relation
public import Slop.Trace.RowContext
public import Slop.UnifiedReduced.Values
public import Slop.UnifiedReduced.ZeroRegister
public import Slop.UnifiedReduced.ControlProjection

@[expose] public section

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
