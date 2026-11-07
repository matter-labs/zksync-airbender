import Airbender.Proofs.Blake2Worker.NativeQueryProjection
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem shape4 {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) (slot : Fin 8) :
    (FlatOperation.lookups (constraintsBlock10 setup)).get ⟨slot.val,by change slot.val < 8; exact slot.isLt⟩ =
      Lookup.mk setup.toRaw (queryFixed4.get slot) := by
  fin_cases slot <;> rfl

theorem fixed4 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed4.get slot).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block10 holds) ⟨slot.val,by change slot.val < 8; exact slot.isLt⟩
  rw [shape4] at query
  exact query

theorem tag4 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed4[slot]).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨200+slot.val,by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [queryFixed4,fixedKind,Fixed.Kind.tag,Expression.eval]

end Airbender.Blake2Worker.QueryProofs
