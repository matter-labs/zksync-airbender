import Airbender.Proofs.Blake2Worker.NativeQueryProjection
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem fixed1_part0 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨0+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨0+slot.val,by change 0+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part0 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨0+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(0+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part1 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨8+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨8+slot.val,by change 8+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part1 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨8+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(8+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part2 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨16+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨16+slot.val,by change 16+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part2 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨16+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(16+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part3 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨24+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨24+slot.val,by change 24+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part3 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨24+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(24+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part4 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨32+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨32+slot.val,by change 32+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part4 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨32+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(32+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part5 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨40+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨40+slot.val,by change 40+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part5 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨40+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(40+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part6 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨48+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨48+slot.val,by change 48+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part6 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨48+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(48+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

private theorem fixed1_part7 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 8) : setup.Contains #[] ((queryFixed1.get ⟨56+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w))) := by
  apply typed_membership
  have query := lookup_of_holds (block7 holds) ⟨56+slot.val,by change 56+slot.val < 64; omega⟩
  fin_cases slot
  all_goals simpa [constraintsBlock7,FlatOperation.lookups,Vector.get,queryFixed1] using query

private theorem tag1_part7 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 8) :
    (((queryFixed1.get ⟨56+slot.val,by have := slot.isLt; omega⟩).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+(56+slot.val),by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  fin_cases slot <;> simp [Vector.get,queryFixed1,fixedKind,Fixed.Kind.tag,Expression.eval]

theorem fixed1 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (slot : Fin 64) : setup.Contains #[] ((queryFixed1.get slot).map (Expression.eval (environment w))) := by
  by_cases h0 : slot.val < 8
  · have result := fixed1_part0 holds ⟨slot.val-0,by omega⟩
    have same : 0+(slot.val-0) = slot.val := by omega
    have position : (⟨0+(slot.val-0),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  by_cases h1 : slot.val < 16
  · have result := fixed1_part1 holds ⟨slot.val-8,by omega⟩
    have same : 8+(slot.val-8) = slot.val := by omega
    have position : (⟨8+(slot.val-8),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  by_cases h2 : slot.val < 24
  · have result := fixed1_part2 holds ⟨slot.val-16,by omega⟩
    have same : 16+(slot.val-16) = slot.val := by omega
    have position : (⟨16+(slot.val-16),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  by_cases h3 : slot.val < 32
  · have result := fixed1_part3 holds ⟨slot.val-24,by omega⟩
    have same : 24+(slot.val-24) = slot.val := by omega
    have position : (⟨24+(slot.val-24),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  by_cases h4 : slot.val < 40
  · have result := fixed1_part4 holds ⟨slot.val-32,by omega⟩
    have same : 32+(slot.val-32) = slot.val := by omega
    have position : (⟨32+(slot.val-32),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  by_cases h5 : slot.val < 48
  · have result := fixed1_part5 holds ⟨slot.val-40,by omega⟩
    have same : 40+(slot.val-40) = slot.val := by omega
    have position : (⟨40+(slot.val-40),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  by_cases h6 : slot.val < 56
  · have result := fixed1_part6 holds ⟨slot.val-48,by omega⟩
    have same : 48+(slot.val-48) = slot.val := by omega
    have position : (⟨48+(slot.val-48),by omega⟩ : Fin 64) = slot := Fin.ext same
    rw [position] at result
    exact result
  have result := fixed1_part7 holds ⟨slot.val-56,by omega⟩
  have same : 56+(slot.val-56) = slot.val := by omega
  have position : (⟨56+(slot.val-56),by omega⟩ : Fin 64) = slot := Fin.ext same
  rw [position] at result
  exact result

theorem tag1 (w : Nat → ZMod mersenne31Modulus) (slot : Fin 64) :
    (((queryFixed1.get slot).map (Expression.eval (environment w)))[3]) =
      ((fixedKind ⟨8+slot.val,by have := slot.isLt; omega⟩).tag : ZMod mersenne31Modulus) := by
  by_cases h0 : slot.val < 8
  · have result := tag1_part0 w ⟨slot.val-0,by omega⟩
    have same : 0+(slot.val-0) = slot.val := by omega
    simpa only [same] using result
  by_cases h1 : slot.val < 16
  · have result := tag1_part1 w ⟨slot.val-8,by omega⟩
    have same : 8+(slot.val-8) = slot.val := by omega
    simpa only [same] using result
  by_cases h2 : slot.val < 24
  · have result := tag1_part2 w ⟨slot.val-16,by omega⟩
    have same : 16+(slot.val-16) = slot.val := by omega
    simpa only [same] using result
  by_cases h3 : slot.val < 32
  · have result := tag1_part3 w ⟨slot.val-24,by omega⟩
    have same : 24+(slot.val-24) = slot.val := by omega
    simpa only [same] using result
  by_cases h4 : slot.val < 40
  · have result := tag1_part4 w ⟨slot.val-32,by omega⟩
    have same : 32+(slot.val-32) = slot.val := by omega
    simpa only [same] using result
  by_cases h5 : slot.val < 48
  · have result := tag1_part5 w ⟨slot.val-40,by omega⟩
    have same : 40+(slot.val-40) = slot.val := by omega
    simpa only [same] using result
  by_cases h6 : slot.val < 56
  · have result := tag1_part6 w ⟨slot.val-48,by omega⟩
    have same : 48+(slot.val-48) = slot.val := by omega
    simpa only [same] using result
  have result := tag1_part7 w ⟨slot.val-56,by omega⟩
  have same : 56+(slot.val-56) = slot.val := by omega
  simpa only [same] using result

end Airbender.Blake2Worker.QueryProofs
