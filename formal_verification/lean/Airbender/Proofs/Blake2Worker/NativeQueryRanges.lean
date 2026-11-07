import Airbender.Proofs.Blake2Worker.NativeQueryProjection
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem scalars_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) (slot : Fin 2) :
    (FlatOperation.lookups (constraintsBlock5 setup)).get ⟨0+slot.val,by change 0+slot.val < 32; omega⟩ =
      range16 (queryScalars.get slot) := by
  fin_cases slot <;> rfl

theorem scalars {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 2) : ((queryScalars.get slot).eval (environment w)).val < 65536 := by
  have query := lookup_of_holds (block5 holds) ⟨0+slot.val,by change 0+slot.val < 32; omega⟩
  rw [scalars_shape] at query
  exact range16_bound query

private theorem clocks0_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) (slot : Fin 30) :
    (FlatOperation.lookups (constraintsBlock5 setup)).get ⟨2+slot.val,by change 2+slot.val < 32; omega⟩ =
      timestamp19 (queryClocks0.get slot) := by
  fin_cases slot <;> rfl

theorem clocks0 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 30) : ((queryClocks0.get slot).eval (environment w)).val < 524288 := by
  have query := lookup_of_holds (block5 holds) ⟨2+slot.val,by change 2+slot.val < 32; omega⟩
  rw [clocks0_shape] at query
  exact timestamp19_bound query

private theorem clocks1_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) (slot : Fin 56) :
    (FlatOperation.lookups (constraintsBlock6 setup)).get ⟨0+slot.val,by change 0+slot.val < 64; omega⟩ =
      timestamp19 (queryClocks1.get slot) := by
  fin_cases slot <;> rfl

theorem clocks1 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 56) : ((queryClocks1.get slot).eval (environment w)).val < 524288 := by
  have query := lookup_of_holds (block6 holds) ⟨0+slot.val,by change 0+slot.val < 64; omega⟩
  rw [clocks1_shape] at query
  exact timestamp19_bound query

end Airbender.Blake2Worker.QueryProofs
