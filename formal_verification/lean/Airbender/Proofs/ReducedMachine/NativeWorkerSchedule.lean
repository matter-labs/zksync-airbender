import Airbender.Review.Circuits.Blake2Worker.Schedule
import Airbender.Proofs.ReducedMachine.NativeMixedReplay

namespace Airbender.NativeWorkerScheduleProofs
open Airbender.NativeWorkerSchedule
open Airbender.Blake2Worker.Native Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Abstract bounded digit window, BEFORE native bit/data instantiation. -/
private theorem digit (whole low bit high : Nat) (slot : Fin 13)
    (lower : low < 2^slot.val) (binary : bit < 2)
    (packed : whole = low + 2^slot.val*bit + 2^(slot.val+1)*high) :
    whole / 2^slot.val % 2 = bit := by
  fin_cases slot <;> norm_num at * <;> omega

/-- Generic canonical bit arithmetic, before actual native/domain data. -/
theorem unpack13 (bits : Nat → Nat) (high : Nat)
    (bounds : ∀ i < 13, bits i ≤ 1)
    (packed : bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 +
      64*bits 6 + 128*bits 7 + 256*bits 8 + 512*bits 9 + 1024*bits 10 + 2048*bits 11 + 4096*bits 12 = high)
    (slot : Fin 13) : high / 2^slot.val % 2 = bits slot.val := by
  have b0 := bounds 0 (by decide +kernel)
  have b1 := bounds 1 (by decide +kernel)
  have b2 := bounds 2 (by decide +kernel)
  have b3 := bounds 3 (by decide +kernel)
  have b4 := bounds 4 (by decide +kernel)
  have b5 := bounds 5 (by decide +kernel)
  have b6 := bounds 6 (by decide +kernel)
  have b7 := bounds 7 (by decide +kernel)
  have b8 := bounds 8 (by decide +kernel)
  have b9 := bounds 9 (by decide +kernel)
  have b10 := bounds 10 (by decide +kernel)
  have b11 := bounds 11 (by decide +kernel)
  have b12 := bounds 12 (by decide +kernel)
  fin_cases slot
  · exact digit high (0) (bits 0) (bits 1 + 2*bits 2 + 4*bits 3 + 8*bits 4 + 16*bits 5 + 32*bits 6 + 64*bits 7 + 128*bits 8 + 256*bits 9 + 512*bits 10 + 1024*bits 11 + 2048*bits 12) ⟨0,by decide +kernel⟩ (by decide +kernel) (by omega) (by norm_num; omega)
  · exact digit high (bits 0) (bits 1) (bits 2 + 2*bits 3 + 4*bits 4 + 8*bits 5 + 16*bits 6 + 32*bits 7 + 64*bits 8 + 128*bits 9 + 256*bits 10 + 512*bits 11 + 1024*bits 12) ⟨1,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1) (bits 2) (bits 3 + 2*bits 4 + 4*bits 5 + 8*bits 6 + 16*bits 7 + 32*bits 8 + 64*bits 9 + 128*bits 10 + 256*bits 11 + 512*bits 12) ⟨2,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2) (bits 3) (bits 4 + 2*bits 5 + 4*bits 6 + 8*bits 7 + 16*bits 8 + 32*bits 9 + 64*bits 10 + 128*bits 11 + 256*bits 12) ⟨3,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3) (bits 4) (bits 5 + 2*bits 6 + 4*bits 7 + 8*bits 8 + 16*bits 9 + 32*bits 10 + 64*bits 11 + 128*bits 12) ⟨4,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4) (bits 5) (bits 6 + 2*bits 7 + 4*bits 8 + 8*bits 9 + 16*bits 10 + 32*bits 11 + 64*bits 12) ⟨5,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5) (bits 6) (bits 7 + 2*bits 8 + 4*bits 9 + 8*bits 10 + 16*bits 11 + 32*bits 12) ⟨6,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 + 64*bits 6) (bits 7) (bits 8 + 2*bits 9 + 4*bits 10 + 8*bits 11 + 16*bits 12) ⟨7,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 + 64*bits 6 + 128*bits 7) (bits 8) (bits 9 + 2*bits 10 + 4*bits 11 + 8*bits 12) ⟨8,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 + 64*bits 6 + 128*bits 7 + 256*bits 8) (bits 9) (bits 10 + 2*bits 11 + 4*bits 12) ⟨9,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 + 64*bits 6 + 128*bits 7 + 256*bits 8 + 512*bits 9) (bits 10) (bits 11 + 2*bits 12) ⟨10,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 + 64*bits 6 + 128*bits 7 + 256*bits 8 + 512*bits 9 + 1024*bits 10) (bits 11) (bits 12) ⟨11,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)
  · exact digit high (bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 + 64*bits 6 + 128*bits 7 + 256*bits 8 + 512*bits 9 + 1024*bits 10 + 2048*bits 11) (bits 12) (0) ⟨12,by decide +kernel⟩ (by norm_num; omega) (by omega) (by norm_num; omega)

theorem next13 (bits : Nat → Nat) (high next : Nat)
    (bounds : ∀ i < 13, bits i ≤ 1)
    (packed : bits 0 + 2*bits 1 + 4*bits 2 + 8*bits 3 + 16*bits 4 + 32*bits 5 +
      64*bits 6 + 128*bits 7 + 256*bits 8 + 512*bits 9 + 1024*bits 10 + 2048*bits 11 + 4096*bits 12 = high)
    (updated : bits 0 + 2*bits 1 + 4*bits 2 + 16*bits 3 + 32*bits 4 + 64*bits 5 +
      128*bits 6 + 256*bits 7 + 512*bits 8 + 1024*bits 9 + 2048*bits 10 + 4096*bits 11 = next) :
    next = nextHigh high := by
  have b0 := bounds 0 (by decide +kernel)
  have b1 := bounds 1 (by decide +kernel)
  have b2 := bounds 2 (by decide +kernel)
  have b3 := bounds 3 (by decide +kernel)
  have b4 := bounds 4 (by decide +kernel)
  have b5 := bounds 5 (by decide +kernel)
  have b6 := bounds 6 (by decide +kernel)
  have b7 := bounds 7 (by decide +kernel)
  have b8 := bounds 8 (by decide +kernel)
  have b9 := bounds 9 (by decide +kernel)
  have b10 := bounds 10 (by decide +kernel)
  have b11 := bounds 11 (by decide +kernel)
  have b12 := bounds 12 (by decide +kernel)
  unfold nextHigh
  omega

theorem flags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (slot : Fin 13) :
    w (138+slot.val) = (inputBit w slot : F) := by
  have same := unpack13 (fun i => (w (138 + i)).val) (w 135).val
    (fun i hi => Airbender.Blake2Worker.NativeProofs.bit_bounds holds ⟨i,hi⟩)
    (Airbender.Blake2Worker.NativeProofs.input_packed holds) slot
  rw [show inputBit w slot = (w (138+slot.val)).val from same]
  exact (ZMod.natCast_zmod_val _).symm

theorem next_control {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    w 136 = 0 ∧ (w 137).val = nextHigh (w 135).val := by
  exact ⟨Airbender.Blake2Worker.NativeProofs.low_cleared holds,
    next13 (fun i => (w (138 + i)).val) (w 135).val (w 137).val
      (fun i hi => Airbender.Blake2Worker.NativeProofs.bit_bounds holds ⟨i,hi⟩)
      (Airbender.Blake2Worker.NativeProofs.input_packed holds)
      (Airbender.Blake2Worker.NativeProofs.output_packed holds)⟩

private theorem block3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock3 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock3 setup).Sublist
      ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup) :=
    List.sublist_append_right _ _
  exact (((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private theorem block4 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock4 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock4 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup) := by
    exact List.sublist_append_right _ _
  exact ((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private def rightSource (w : Nat → F) (piece : Fin 32) : F :=
  if piece.val < 16 then w (102+piece.val) else w (4+4*((piece.val-16)/2)+piece.val%2)
private def leftSource (w : Nat → F) (piece : Fin 32) : F :=
  if piece.val < 16 then w (4+4*(piece.val/2)+piece.val%2) else w (86+piece.val)
private def maskFormula (w : Nat → F) (piece : Fin 32) : Prop :=
  w (204+piece.val) = (1-w 140)*w (102+piece.val) + w 202*rightSource w piece + w 203*leftSource w piece

private theorem mask_part0 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    maskFormula w ⟨0 + i.val,by have := i.isLt; omega⟩ := by
  have equation := assertion_of_holds (block3 holds) ⟨29 + i.val,by change 29 + i.val < 64; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [maskFormula,rightSource,leftSource]
    linear_combination -equation

private theorem mask_part1 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    maskFormula w ⟨8 + i.val,by have := i.isLt; omega⟩ := by
  have equation := assertion_of_holds (block3 holds) ⟨37 + i.val,by change 37 + i.val < 64; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [maskFormula,rightSource,leftSource]
    linear_combination -equation

private theorem mask_part2 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    maskFormula w ⟨16 + i.val,by have := i.isLt; omega⟩ := by
  have equation := assertion_of_holds (block3 holds) ⟨45 + i.val,by change 45 + i.val < 64; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [maskFormula,rightSource,leftSource]
    linear_combination -equation

private theorem mask_part3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    maskFormula w ⟨24 + i.val,by have := i.isLt; omega⟩ := by
  have equation := assertion_of_holds (block3 holds) ⟨53 + i.val,by change 53 + i.val < 64; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [maskFormula,rightSource,leftSource]
    linear_combination -equation

private theorem mask_all {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (piece : Fin 32) : maskFormula w piece := by
  by_cases h0 : piece.val < 8
  · have localIndex : piece.val-0 < 8 := by have := piece.isLt; omega
    have same : (⟨0+(piece.val-0),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 0+(piece.val-0) = piece.val; omega
    exact same ▸ mask_part0 holds ⟨piece.val-0,localIndex⟩
  by_cases h1 : piece.val < 16
  · have localIndex : piece.val-8 < 8 := by have := piece.isLt; omega
    have same : (⟨8+(piece.val-8),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 8+(piece.val-8) = piece.val; omega
    exact same ▸ mask_part1 holds ⟨piece.val-8,localIndex⟩
  by_cases h2 : piece.val < 24
  · have localIndex : piece.val-16 < 8 := by have := piece.isLt; omega
    have same : (⟨16+(piece.val-16),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 16+(piece.val-16) = piece.val; omega
    exact same ▸ mask_part2 holds ⟨piece.val-16,localIndex⟩
  have localIndex : piece.val-24 < 8 := by have := piece.isLt; omega
  have same : (⟨24+(piece.val-24),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 24+(piece.val-24) = piece.val; omega
  exact same ▸ mask_part3 holds ⟨piece.val-24,localIndex⟩

private theorem compression_flags {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    w 202 = w 139*w 140 ∧ w 203 = w 140-w 139*w 140 := by
  have right := assertion_of_holds (block3 holds) ⟨27,by change 27 < 64; decide +kernel⟩
  have left := assertion_of_holds (block3 holds) ⟨28,by change 28 < 64; decide +kernel⟩
  simp [constraintsBlock3,FlatOperation.constraints,Expression.eval,environment] at right left
  exact ⟨by linear_combination -right,by linear_combination -left⟩

/-- All32 masked limbs select actual original state/message operands. -/
theorem masked_inputs {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (word : Fin 16) (limb : Fin 2) : w (204+2*word.val+limb.val) = input w word limb := by
  have boundWord := word.isLt
  have boundLimb := limb.isLt
  let piece : Fin 32 := ⟨2*word.val+limb.val,by omega⟩
  have equation := mask_all holds piece
  have selectors := compression_flags holds
  have compression := flags holds 2
  have right := flags holds 1
  change w 140 = (inputBit w 2 : F) at compression
  change w 139 = (inputBit w 1 : F) at right
  have bc : inputBit w 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide +kernel))
  have br : inputBit w 1 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide +kernel))
  have divide : (2*word.val+limb.val)/2 = word.val := by omega
  have modulo : (2*word.val+limb.val)%2 = limb.val := by omega
  have divideTail : (2*word.val+limb.val-16)/2 = word.val-8 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bc with c | c <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp br with r | r
  all_goals
    rw [c] at compression
    rw [r] at right
    simp only [Nat.cast_zero,Nat.cast_one] at compression right
    simp only [maskFormula,piece] at equation
    rw [selectors.1,selectors.2,compression,right] at equation
    by_cases half : word.val < 8
    · have first : 2*word.val+limb.val < 16 := by omega
      simp [input,c,r,message,state,rightSource,leftSource,half,first,divide,modulo,Nat.add_assoc] at equation ⊢
      exact equation
    · have last : ¬ 2*word.val+limb.val < 16 := by omega
      have index : 86+(2*word.val+limb.val) = 102+2*(word.val-8)+limb.val := by omega
      simp [input,c,r,message,state,rightSource,leftSource,half,last,divideTail,modulo,index,Nat.add_assoc] at equation ⊢
      exact equation


private def permutationExpr (setup : Table F (fields 4)) (piece : Fin 32) : Expression F :=
  if h : piece.val < 3 then
    (FlatOperation.constraints (constraintsBlock3 setup)).get ⟨61+piece.val,by change 61+piece.val < 64; omega⟩
  else (FlatOperation.constraints (constraintsBlock4 setup)).get ⟨piece.val-3,by change piece.val-3 < 64; have := piece.isLt; omega⟩

private theorem permutation_assert {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (piece : Fin 32) :
    (permutationExpr setup piece).eval (environment w) = 0 := by
  unfold permutationExpr
  split
  · exact assertion_of_holds (block3 holds) _
  · exact assertion_of_holds (block4 holds) _

private def rawPermutation (w : Nat → F) (piece : Fin 32) : Prop :=
  w (236+piece.val) = ∑ round : Fin 10, w (141+round.val) *
    w (204+2*(sigma[round][(⟨piece.val/2,by have := piece.isLt; omega⟩ : Fin 16)]).val+piece.val%2)

private theorem permutation_part0 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    rawPermutation w ⟨0 + i.val,by have := i.isLt; omega⟩ := by
  have equation := permutation_assert holds ⟨0 + i.val,by have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [permutationExpr,constraintsBlock3,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [rawPermutation,sigma,Fin.sum_univ_succ]
    linear_combination -equation

private theorem permutation_part1 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    rawPermutation w ⟨8 + i.val,by have := i.isLt; omega⟩ := by
  have equation := permutation_assert holds ⟨8 + i.val,by have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [permutationExpr,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [rawPermutation,sigma,Fin.sum_univ_succ]
    linear_combination -equation

private theorem permutation_part2 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    rawPermutation w ⟨16 + i.val,by have := i.isLt; omega⟩ := by
  have equation := permutation_assert holds ⟨16 + i.val,by have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [permutationExpr,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [rawPermutation,sigma,Fin.sum_univ_succ]
    linear_combination -equation

private theorem permutation_part3 {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (i : Fin 8) :
    rawPermutation w ⟨24 + i.val,by have := i.isLt; omega⟩ := by
  have equation := permutation_assert holds ⟨24 + i.val,by have := i.isLt; omega⟩
  fin_cases i
  all_goals
    simp [permutationExpr,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at equation
    simp [rawPermutation,sigma,Fin.sum_univ_succ]
    linear_combination -equation

private theorem permutation_all {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (piece : Fin 32) : rawPermutation w piece := by
  by_cases h0 : piece.val < 8
  · have localIndex : piece.val-0 < 8 := by have := piece.isLt; omega
    have same : (⟨0+(piece.val-0),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 0+(piece.val-0) = piece.val; omega
    exact same ▸ permutation_part0 holds ⟨piece.val-0,localIndex⟩
  by_cases h1 : piece.val < 16
  · have localIndex : piece.val-8 < 8 := by have := piece.isLt; omega
    have same : (⟨8+(piece.val-8),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 8+(piece.val-8) = piece.val; omega
    exact same ▸ permutation_part1 holds ⟨piece.val-8,localIndex⟩
  by_cases h2 : piece.val < 24
  · have localIndex : piece.val-16 < 8 := by have := piece.isLt; omega
    have same : (⟨16+(piece.val-16),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 16+(piece.val-16) = piece.val; omega
    exact same ▸ permutation_part2 holds ⟨piece.val-16,localIndex⟩
  have localIndex : piece.val-24 < 8 := by have := piece.isLt; omega
  have same : (⟨24+(piece.val-24),by omega⟩ : Fin 32) = piece := by apply Fin.ext; change 24+(piece.val-24) = piece.val; omega
  exact same ▸ permutation_part3 holds ⟨piece.val-24,localIndex⟩

/-- Every actual selected limb equals the full Boolean-weighted native schedule.
    No one-hot, expected round, read value or hash output is a premise. -/
theorem permutation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (word : Fin 16) (limb : Fin 2) : selected w word limb = scheduled w word limb := by
  have bw := word.isLt
  have bl := limb.isLt
  let piece : Fin 32 := ⟨2*word.val+limb.val,by omega⟩
  have equation := permutation_all holds piece
  have divide : (2*word.val+limb.val)/2 = word.val := by omega
  have modulo : (2*word.val+limb.val)%2 = limb.val := by omega
  have observed : selected w word limb = ∑ round : Fin 10, w (141+round.val) *
      w (204+2*(sigma[round][word]).val+limb.val) := by
    simpa only [rawPermutation,piece,divide,modulo,selected,Nat.add_assoc] using equation
  rw [observed]
  unfold scheduled
  apply Finset.sum_congr rfl
  intro round _
  have flag : w (141+round.val) = (inputBit w ⟨3+round.val,by omega⟩ : F) := by
    simpa only [← Nat.add_assoc,Nat.reduceAdd] using flags holds ⟨3+round.val,by omega⟩
  rw [flag,masked_inputs holds]


theorem row {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : RowEffects w :=
  ⟨Airbender.Blake2Worker.NativeProofs.effects holds,flags holds,masked_inputs holds,permutation holds,next_control holds⟩

open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, RowEffects w := by
  have prior := Airbender.NativeMixedReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior,fun w member => row (processing w member).body⟩
end Airbender.NativeWorkerScheduleProofs
