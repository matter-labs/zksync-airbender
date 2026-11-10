import Airbender.Proofs.Bigint.MultiplicationColumnsBase
namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

/-- The same imported multiplication assertions, checked four columns at a time. -/
theorem native_columns_chunk7 {w : Nat → ZMod babyBearModulus} {left right : Fin 16 → Nat}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (sources : ∀ i, w Variables.leftLimbs[i] = (left i : ZMod babyBearModulus) ∧
      w Variables.rightLimbs[i] = (right i : ZMod babyBearModulus))
    (bytes : ∀ i : Fin 16,
      w (99 + i.val) = ((left i % 256 : Nat) : ZMod babyBearModulus) ∧
      w (115 + i.val) = ((right i % 256 : Nat) : ZMod babyBearModulus)) :
    ∀ lane : Fin 4, let i := columnIndex (7 : Fin 8) lane
    (multiplicationColumn left right i.val : ZMod babyBearModulus) + incoming w i =
      w (131 + i.val) + 65536 * outgoing w i := by
  have leftAssembly (i : Fin 16) : w Variables.leftLimbs[i] =
      ((left i % 256 : Nat) : ZMod babyBearModulus) +
        256 * ((left i / 256 : Nat) : ZMod babyBearModulus) := by
    rw [(sources i).1]
    have split := congrArg (fun n : Nat => (n : ZMod babyBearModulus)) (Nat.mod_add_div (left i) 256)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using split.symm
  have rightAssembly (i : Fin 16) : w Variables.rightLimbs[i] =
      ((right i % 256 : Nat) : ZMod babyBearModulus) +
        256 * ((right i / 256 : Nat) : ZMod babyBearModulus) := by
    rw [(sources i).2]
    have split := congrArg (fun n : Nat => (n : ZMod babyBearModulus)) (Nat.mod_add_div (right i) 256)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using split.symm
  have l0 := leftAssembly ⟨0, by decide⟩
  have r0 := rightAssembly ⟨0, by decide⟩
  have q0 := bytes ⟨0, by decide⟩
  have l1 := leftAssembly ⟨1, by decide⟩
  have r1 := rightAssembly ⟨1, by decide⟩
  have q1 := bytes ⟨1, by decide⟩
  have l2 := leftAssembly ⟨2, by decide⟩
  have r2 := rightAssembly ⟨2, by decide⟩
  have q2 := bytes ⟨2, by decide⟩
  have l3 := leftAssembly ⟨3, by decide⟩
  have r3 := rightAssembly ⟨3, by decide⟩
  have q3 := bytes ⟨3, by decide⟩
  have l4 := leftAssembly ⟨4, by decide⟩
  have r4 := rightAssembly ⟨4, by decide⟩
  have q4 := bytes ⟨4, by decide⟩
  have l5 := leftAssembly ⟨5, by decide⟩
  have r5 := rightAssembly ⟨5, by decide⟩
  have q5 := bytes ⟨5, by decide⟩
  have l6 := leftAssembly ⟨6, by decide⟩
  have r6 := rightAssembly ⟨6, by decide⟩
  have q6 := bytes ⟨6, by decide⟩
  have l7 := leftAssembly ⟨7, by decide⟩
  have r7 := rightAssembly ⟨7, by decide⟩
  have q7 := bytes ⟨7, by decide⟩
  have l8 := leftAssembly ⟨8, by decide⟩
  have r8 := rightAssembly ⟨8, by decide⟩
  have q8 := bytes ⟨8, by decide⟩
  have l9 := leftAssembly ⟨9, by decide⟩
  have r9 := rightAssembly ⟨9, by decide⟩
  have q9 := bytes ⟨9, by decide⟩
  have l10 := leftAssembly ⟨10, by decide⟩
  have r10 := rightAssembly ⟨10, by decide⟩
  have q10 := bytes ⟨10, by decide⟩
  have l11 := leftAssembly ⟨11, by decide⟩
  have r11 := rightAssembly ⟨11, by decide⟩
  have q11 := bytes ⟨11, by decide⟩
  have l12 := leftAssembly ⟨12, by decide⟩
  have r12 := rightAssembly ⟨12, by decide⟩
  have q12 := bytes ⟨12, by decide⟩
  have l13 := leftAssembly ⟨13, by decide⟩
  have r13 := rightAssembly ⟨13, by decide⟩
  have q13 := bytes ⟨13, by decide⟩
  have l14 := leftAssembly ⟨14, by decide⟩
  have r14 := rightAssembly ⟨14, by decide⟩
  have q14 := bytes ⟨14, by decide⟩
  have l15 := leftAssembly ⟨15, by decide⟩
  have r15 := rightAssembly ⟨15, by decide⟩
  have q15 := bytes ⟨15, by decide⟩
  norm_num [Variables.leftLimbs, Variables.rightLimbs] at l0 r0 q0 l1 r1 q1 l2 r2 q2 l3 r3 q3 l4 r4 q4 l5 r5 q5 l6 r6 q6 l7 r7 q7 l8 r8 q8 l9 r9 q9 l10 r10 q10 l11 r11 q11 l12 r12 q12 l13 r13 q13 l14 r14 q14 l15 r15 q15
  have characteristic : (2013265921 : ZMod babyBearModulus) = 0 := by decide
  intro lane
  let i := columnIndex (7 : Fin 8) lane
  let index := i.val
  have indexBound : index < 32 := i.isLt
  fin_cases lane
  all_goals have gate := Verification.assertion_of_holds h ⟨19 + index,
    by rw [constraint_count]; omega⟩
  all_goals simp [importedConstraints, FlatOperation.constraints, index, i, columnIndex, Expression.eval,
    Verification.environment] at gate
  all_goals simp only [l12, r12, q12.1, q12.2, l13, r13, q13.1, q13.2, l14, r14, q14.1, q14.2, l15, r15, q15.1, q15.2] at gate
  all_goals norm_num [multiplicationColumn, diagonal, byteCross, byteHigh, Fin.sum_univ_succ, Fin.succ,
    incoming, outgoing, carry, babyBearModulus, i, columnIndex]
  all_goals linear_combination (norm := ring_nf) gate
  all_goals rw [characteristic]
  all_goals simp

end Airbender.Bigint.Multiplication.Proofs
