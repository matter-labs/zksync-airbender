module
public import Human.Circuits.UnifiedReduced.Delegation
public import Slop.JumpBranchSlt
public import Slop.ShiftBinop
public import Slop.Trace.Program
public import Slop.UnifiedReduced
public import Slop.AddSub.PC
public import Slop.Delegation.CallerRequests

@[expose] public section

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem caller_zeroes [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 18 = 1) :
    w 42 = 0 ∧ w 43 = 0 ∧ w 40 = 0 ∧ w 41 = 0 ∧ w 50 = 0 ∧ w 51 = 0 := by
  have eq6 := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have eq7 := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have eq8 := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have eq9 := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  have eq10 := Verification.assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
  have eq11 := Verification.assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at eq6 eq7 eq8 eq9 eq10 eq11
  exact ⟨eq6, eq7, eq8, eq9, eq10, eq11⟩

end Airbender.UnifiedReduced.Caller.Proofs
