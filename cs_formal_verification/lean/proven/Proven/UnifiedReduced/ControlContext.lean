module
public import Mathlib.Logic.Relation
public import Human.Helpers.Properties
public import Proven.Constraints
public import Proven.KernelRfl
public import Proven.UnifiedReduced.ArtifactChecks
public import Proven.UnifiedReduced.OpIndex
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Proven.CleanCore.Circuit.Operations

public import Proven.UnifiedReduced.Standard.Artifact
public meta import Proven.UnifiedReduced.Standard.Instances

@[expose] public section

namespace Airbender.UnifiedReduced.Standard.Control.Proofs
variable {profile : Profile}
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

theorem right_sign_source [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints profile setup))
    (selected : w 21 + w 22 + w 23 + w 24 = 1) : w 60 = w 43 + w 23 * w 9 := by
  have gate := Verification.assertion_of_holds holds ⟨14, by rw [constraint_count]; decide⟩
  op_index at gate
  simp [Expression.eval, Verification.environment, selected] at gate
  linear_combination gate

babybear_instances right_sign_source

end Airbender.UnifiedReduced.Standard.Control.Proofs
