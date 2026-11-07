import Airbender.Proofs.Blake2Worker.NativeQueryProjection
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem shape2 {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) (slot : Fin 64) :
    (FlatOperation.lookups (constraintsBlock8 setup)).get ⟨slot.val,by change slot.val < 64; exact slot.isLt⟩ =
      Lookup.mk setup.toRaw (queryFixed2.get slot) := by
  fin_cases slot <;> rfl

theorem fixed2 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 64) : setup.Contains #[] ((queryFixed2.get slot).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block8 holds) ⟨slot.val,by change slot.val < 64; exact slot.isLt⟩
  rw [shape2] at query
  exact query

private theorem tag2_part0 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨0+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(0+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part1 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨8+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(8+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part2 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨16+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(16+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part3 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨24+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(24+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part4 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨32+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(32+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part5 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨40+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(40+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part6 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨48+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(48+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem tag2_part7 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed2.get ⟨56+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+(56+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed2,fixedKind,Fixed.Kind.tag,Expression.eval]

theorem tag2 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 64) :
    (((queryFixed2.get slot).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨72+slot.val,by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  by_cases h0 : slot.val < 8
  · have result := tag2_part0 w ⟨slot.val-0,by omega⟩
    have same : 0+(slot.val-0) = slot.val := by omega
    simpa only [same] using result
  by_cases h1 : slot.val < 16
  · have result := tag2_part1 w ⟨slot.val-8,by omega⟩
    have same : 8+(slot.val-8) = slot.val := by omega
    simpa only [same] using result
  by_cases h2 : slot.val < 24
  · have result := tag2_part2 w ⟨slot.val-16,by omega⟩
    have same : 16+(slot.val-16) = slot.val := by omega
    simpa only [same] using result
  by_cases h3 : slot.val < 32
  · have result := tag2_part3 w ⟨slot.val-24,by omega⟩
    have same : 24+(slot.val-24) = slot.val := by omega
    simpa only [same] using result
  by_cases h4 : slot.val < 40
  · have result := tag2_part4 w ⟨slot.val-32,by omega⟩
    have same : 32+(slot.val-32) = slot.val := by omega
    simpa only [same] using result
  by_cases h5 : slot.val < 48
  · have result := tag2_part5 w ⟨slot.val-40,by omega⟩
    have same : 40+(slot.val-40) = slot.val := by omega
    simpa only [same] using result
  by_cases h6 : slot.val < 56
  · have result := tag2_part6 w ⟨slot.val-48,by omega⟩
    have same : 48+(slot.val-48) = slot.val := by omega
    simpa only [same] using result
  have result := tag2_part7 w ⟨slot.val-56,by omega⟩
  have same : 56+(slot.val-56) = slot.val := by omega
  simpa only [same] using result

end Airbender.Blake2Worker.QueryProofs
