import Airbender.Proofs.Blake2Worker.NativeQueryProjection
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem fixed0 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed0[slot]).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block6 holds) ⟨56+slot.val,by change 56+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock6,FlatOperation.lookups,queryFixed0] using query

theorem tag0 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed0[slot]).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨0+slot.val,by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [queryFixed0,fixedKind,Fixed.Kind.tag,Expression.eval]

end Airbender.Blake2Worker.QueryProofs
