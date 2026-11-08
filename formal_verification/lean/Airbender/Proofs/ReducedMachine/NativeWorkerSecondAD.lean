import Airbender.Review.Circuits.Blake2Worker.SecondAD
import Airbender.Proofs.ReducedMachine.NativeWorkerCB

namespace Airbender.NativeWorkerSecondADProofs
open Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem rotate8 (b0 b1 b2 b3 : BitVec 8) :
    BitVec.append (BitVec.append b0 b3) (BitVec.append b2 b1) =
      (BitVec.append (BitVec.append b3 b2) (BitVec.append b1 b0)).rotateRight 8 := by
  have p16 (a b : BitVec 8) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 8 then b.getLsbD j else a.getLsbD (j-8) := BitVec.getLsbD_append
  have p32 (a b : BitVec 16) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 16 then b.getLsbD j else a.getLsbD (j-16) := BitVec.getLsbD_append
  have rot (x : BitVec 32) (j : Nat) (bound : j < 32) :
      (x.rotateRight 8).getLsbD j = if j < 24 then x.getLsbD (8+j) else x.getLsbD (j-24) := by
    rw [BitVec.getLsbD_rotateRight_of_lt (by decide +kernel)]
    by_cases cut : j < 24
    · simp [cut]
    · simp [cut,bound]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  rw [rot _ _ (by omega)]
  simp only [p32,p16]
  split_ifs <;> congr 1 <;> omega

theorem rotated_half (a b c : F) (ab : a.val < 16) (bb : b.val < 8) (cb : c.val < 512) :
    (a+16*b+128*c).val < 65536 ∧
    BitVec.ofNat 16 (a+16*b+128*c).val = BitVec.append
      (BitVec.append (BitVec.ofNat 9 c.val) (BitVec.ofNat 3 b.val)) (BitVec.ofNat 4 a.val) := by
  have bound : a.val+16*b.val+128*c.val < 65536 := by omega
  have same : a+16*b+128*c = ((a.val+16*b.val+128*c.val : Nat) : F) := by simp
  have canonical : (a+16*b+128*c).val = a.val+16*b.val+128*c.val := by
    rw [same,ZMod.val_natCast_of_lt (bound.trans (by decide +kernel))]
  refine ⟨by omega,?_⟩
  apply BitVec.eq_of_toNat_eq
  change (a+16*b+128*c).val%65536 = ((((c.val%512) <<< 3) ||| (b.val%8)) <<< 4) ||| (a.val%16)
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show b.val%8 < 2^3 by omega)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show a.val%16 < 2^4 by omega)]
  simp [canonical,Nat.shiftLeft_eq,Nat.mod_eq_of_lt ab,Nat.mod_eq_of_lt bb,Nat.mod_eq_of_lt cb,Nat.mod_eq_of_lt bound]
  omega

open Airbender.NativeWorkerSecondAD Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
open Airbender.Blake2Worker.Native
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_one : (2147483648 : F) = 1 := by decide +kernel
@[simp] private theorem coefficient_two : (4294967296 : F) = 2 := by decide +kernel
@[simp] private theorem scale256 : (549755813888 : F) = 256 := by decide +kernel
@[simp] private theorem scale16 : (34359738368 : F) = 16 := by decide +kernel
@[simp] private theorem scale128 : (274877906688 : F) = -128 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 16 := #v[
#v[(.var ⟨278⟩),(.var ⟨300⟩),(.var ⟨302⟩)],
#v[(.var ⟨279⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨155⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨171⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨236⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨238⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨290⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨293⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨294⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨300⟩))),(.var ⟨303⟩)],
#v[(.var ⟨275⟩),(.var ⟨301⟩),(.var ⟨304⟩)],
#v[(.var ⟨276⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨157⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨173⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨237⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨239⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨270⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨271⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨288⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨289⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨295⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨298⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨299⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨301⟩))),(.var ⟨305⟩)],
#v[(.var ⟨324⟩),(.var ⟨346⟩),(.var ⟨348⟩)],
#v[(.var ⟨325⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨159⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨175⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨240⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨242⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨336⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨339⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨340⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨346⟩))),(.var ⟨349⟩)],
#v[(.var ⟨321⟩),(.var ⟨347⟩),(.var ⟨350⟩)],
#v[(.var ⟨322⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨161⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨177⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨241⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨243⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨316⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨317⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨334⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨335⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨341⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨344⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨345⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨347⟩))),(.var ⟨351⟩)],
#v[(.var ⟨370⟩),(.var ⟨392⟩),(.var ⟨394⟩)],
#v[(.var ⟨371⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨163⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨179⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨244⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨246⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨382⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨385⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨386⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨392⟩))),(.var ⟨395⟩)],
#v[(.var ⟨367⟩),(.var ⟨393⟩),(.var ⟨396⟩)],
#v[(.var ⟨368⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨165⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨181⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨245⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨247⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨362⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨363⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨380⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨381⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨387⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨390⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨391⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨393⟩))),(.var ⟨397⟩)],
#v[(.var ⟨416⟩),(.var ⟨438⟩),(.var ⟨440⟩)],
#v[(.var ⟨417⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨167⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨183⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨248⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨250⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨428⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨431⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨432⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨438⟩))),(.var ⟨441⟩)],
#v[(.var ⟨413⟩),(.var ⟨439⟩),(.var ⟨442⟩)],
#v[(.var ⟨414⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨169⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨185⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨249⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨251⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨408⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨409⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨426⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨427⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨433⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨436⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨437⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨439⟩))),(.var ⟨443⟩)]]

/-- Exact actual query syntax is bound BEFORE witness evaluation. -/
private theorem shape (column : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨10+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
    sourceExpressions[(⟨4*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  fin_cases column <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value (w : Nat → F) (column : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (query w column piece)[entry.val]'(by have := entry.isLt; omega) =
    Expression.eval (environment w) sourceExpressions[(⟨4*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece entry)

private theorem value0 (w : Nat → F) (column : Fin 4) (piece : Fin 4) :
    (query w column piece)[0] = Expression.eval (environment w)
      sourceExpressions[(⟨4*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 16)][0] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece 0)

private theorem value1 (w : Nat → F) (column : Fin 4) (piece : Fin 4) :
    (query w column piece)[1] = Expression.eval (environment w)
      sourceExpressions[(⟨4*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 16)][1] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece 1)

private theorem value2 (w : Nat → F) (column : Fin 4) (piece : Fin 4) :
    (query w column piece)[2] = Expression.eval (environment w)
      sourceExpressions[(⟨4*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 16)][2] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece 2)

private theorem sum_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    sumLimb w column limb = (query w column ⟨2*limb.val,by have := limb.isLt; omega⟩)[1] +
      256*(query w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w column _,value1 w column _]
  fin_cases column <;> fin_cases limb
  all_goals
    simp [sumLimb,bInput,carry,Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,observed,initialColumns,selected,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem d_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    dInput w column limb = (query w column ⟨2*limb.val,by have := limb.isLt; omega⟩)[0] +
      256*(query w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w column _,value0 w column _]
  fin_cases column <;> fin_cases limb
  all_goals
    simp [dInput,Airbender.NativeWorkerCB.dLimb,Airbender.NativeWorkerCB.dByte,sourceExpressions,Expression.eval,environment]
private theorem block0 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock0 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock0 setup).Sublist ([] ++ constraintsBlock0 setup) := by
    simp
  exact ((((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


theorem carry_bits {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (column : Fin 4) (slot : Fin 4) : (carryBit w column slot).val ≤ 1 := by
  have bit := assertion_of_holds (block0 holds) ⟨19+12*column.val+slot.val,by change 19+12*column.val+slot.val < 64; have := column.isLt; have := slot.isLt; omega⟩
  fin_cases column <;> fin_cases slot
  all_goals
    simp [constraintsBlock0,FlatOperation.constraints,Expression.eval,environment,carryBit] at bit ⊢
    obtain ⟨n,bound,same⟩ := Arithmetic.boolean_nat (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

private theorem byte_effects {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (piece : Fin 4) :
    (query w column piece)[0].val < 256 ∧ (query w column piece)[1].val < 256 ∧
    (query w column piece)[2].val < 256 ∧
    (query w column piece)[2].val = (query w column piece)[0].val ^^^ (query w column piece)[1].val := by
  let slot : Fin 208 := ⟨10+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases column <;> fin_cases piece <;> norm_num [fixedKind]
  exact ⟨by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.leftBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.rightBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.outputBounds slot,
    effects.results slot⟩

private theorem output_value (w : Nat → F) (column : Fin 4) (piece : Fin 4) :
    (query w column piece)[2] = w (302+46*column.val+piece.val) := by
  rw [value2 w column piece]
  fin_cases column <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (sumLimb w column limb).val < 65536 ∧ (dInput w column limb).val < 65536 := by
  have low := byte_effects effects column ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := byte_effects effects column ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  constructor
  · rw [sum_reconstruction]
    exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)
  · rw [d_reconstruction]
    exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)

private theorem xor_bytes (a b c d : BitVec 8) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor_halves (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append

private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (dInput w column limb).val ^^^ BitVec.ofNat 16 (sumLimb w column limb).val) =
    BitVec.append (byte w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)
      (byte w column ⟨2*limb.val,by have := limb.isLt; omega⟩) := by
  let low : Fin 4 := ⟨2*limb.val,by have := limb.isLt; omega⟩
  let high : Fin 4 := ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  have l := byte_effects effects column low
  have h := byte_effects effects column high
  have d := Airbender.NativeWorkerFirstGProofs.pair_bytes (dInput w column limb) _ _ l.1 h.1 (d_reconstruction w column limb)
  have a := Airbender.NativeWorkerFirstGProofs.pair_bytes (sumLimb w column limb) _ _ l.2.1 h.2.1 (sum_reconstruction w column limb)
  have out0 := Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ l.1 l.2.1 l.2.2.1 l.2.2.2
  have out1 := Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2
  rw [output_value] at out0 out1
  rw [d,a,xor_bytes,← out0,← out1]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    dAfter w column = (Airbender.NativeWorkerFirstG.pack (dInput w column 0) (dInput w column 1) ^^^
      Airbender.NativeWorkerFirstG.pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 8 := by
  unfold dAfter Airbender.NativeWorkerFirstG.pack
  rw [xor_halves,half_xor effects,half_xor effects,← rotate8]
  rfl



/-- Specific original B-output syntax, bound before sampling any witness. -/
private theorem b_shape (column : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (fixedExpressions ⟨4+18*column.val+(3*limb.val+piece.val),by have := column.isLt; have := limb.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨288+46*column.val+5*limb.val+piece.val⟩ := by
  fin_cases column <;> fin_cases limb <;> fin_cases piece <;> rfl
private theorem b_output_bounds {w : Nat → F} (effects : LookupEffects w)
    (column : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (w (288+46*column.val+5*limb.val+piece.val)).val < (#v[8,512,16] : Vector Nat 3)[piece] := by
  let slot : Fin 208 := ⟨4+18*column.val+(3*limb.val+piece.val),by have := column.isLt; have := limb.isLt; have := piece.isLt; omega⟩
  have bound : (fixedKind slot).bound = (#v[8,512,16] : Vector Nat 3)[piece] := by
    dsimp only [slot]
    fin_cases column <;> fin_cases limb <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound]
  have same : (fixedQuery w slot)[2] = w (288+46*column.val+5*limb.val+piece.val) := by
    simpa [fixedQuery,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (b_shape column limb piece)
  have h := effects.outputBounds slot
  rw [same,bound] at h
  exact h

theorem b_halves {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    (bInput w column 0).val < 65536 ∧ (bInput w column 1).val < 65536 ∧
      Airbender.NativeWorkerFirstG.pack (bInput w column 0) (bInput w column 1) = Airbender.NativeWorkerCB.bAfter w column := by
  have l0 := b_output_bounds effects column 0 0
  have l1 := b_output_bounds effects column 0 1
  have l2 := b_output_bounds effects column 0 2
  have h0 := b_output_bounds effects column 1 0
  have h1 := b_output_bounds effects column 1 1
  have h2 := b_output_bounds effects column 1 2
  change (w (288+46*column.val)).val < 8 at l0
  change (w (288+46*column.val+1)).val < 512 at l1
  change (w (288+46*column.val+2)).val < 16 at l2
  change (w (288+46*column.val+5)).val < 8 at h0
  change (w (288+46*column.val+6)).val < 512 at h1
  change (w (288+46*column.val+7)).val < 16 at h2
  have c1 : 288+46*column.val+1 = 289+46*column.val := by omega
  have c2 : 288+46*column.val+2 = 290+46*column.val := by omega
  have c5 : 288+46*column.val+5 = 293+46*column.val := by omega
  have c6 : 288+46*column.val+6 = 294+46*column.val := by omega
  have c7 : 288+46*column.val+7 = 295+46*column.val := by omega
  rw [c1] at l1
  rw [c2] at l2
  rw [c5] at h0
  rw [c6] at h1
  rw [c7] at h2
  have low := rotated_half _ _ _ l2 h0 h1
  have high := rotated_half _ _ _ h2 l0 l1
  refine ⟨low.1,high.1,?_⟩
  change BitVec.append (BitVec.ofNat 16 (w (295+46*column.val)+16*w (288+46*column.val)+128*w (289+46*column.val)).val)
    (BitVec.ofNat 16 (w (290+46*column.val)+16*w (293+46*column.val)+128*w (294+46*column.val)).val) = _
  rw [low.2,high.2]
  simp only [Airbender.NativeWorkerCB.bAfter,Airbender.NativeWorkerCB.chunk9,
    Airbender.NativeWorkerCB.chunk3,Airbender.NativeWorkerCB.chunk4]
  have d6 : 289+46*column.val+5 = 294+46*column.val := by omega
  have d7 : 290+46*column.val+5 = 295+46*column.val := by omega
  change _ = BitVec.append
    (BitVec.append (BitVec.append (BitVec.ofNat 9 (w (289+46*column.val)).val) (BitVec.ofNat 3 (w (288+46*column.val)).val)) (BitVec.ofNat 4 (w (290+46*column.val+5)).val))
    (BitVec.append (BitVec.append (BitVec.ofNat 9 (w (289+46*column.val+5)).val) (BitVec.ofNat 3 (w (288+46*column.val+5)).val)) (BitVec.ofNat 4 (w (290+46*column.val)).val))
  rw [c5,d6,d7]

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem carry_bounds {w : Nat → F} (effects : LocalEffects w) (column : Fin 4) (limb : Fin 2) :
    (carry w column limb).val ≤ 3 := by
  have low := effects.carries column ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := effects.carries column ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  dsimp [carryBit] at low high
  have high' : (w (297+46*column.val+2*limb.val)).val ≤ 1 := by
    rw [show 297+46*column.val+2*limb.val = 296+46*column.val+(2*limb.val+1) by omega]
    exact high
  exact (Airbender.NativeWorkerAdditionProofs.carry_value _ _ low high').2

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerCB.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (column : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (sumLimb w column 0) (sumLimb w column 1) =
      Airbender.NativeWorkerAddition.aAfter w column + Airbender.NativeWorkerCB.bAfter w column +
        Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val+1,by have := column.isLt; omega⟩ := by
  let m : Fin 16 := ⟨2*column.val+1,by have := column.isLt; omega⟩
  have ab (limb : Fin 2) := (prior.prior.prior.bounds column limb).1
  have bb := b_halves effects column
  have mb (limb : Fin 2) : (selected w m limb).val < 655360 := by
    rw [(prior.prior.selected m limb).1]
    exact (prior.prior.selected m limb).2
  have field (limb : Fin 2) :
      Airbender.NativeWorkerFirstG.sumLimb w column limb + bInput w column limb + selected w m limb +
        (if limb.val = 0 then 0 else carry w column 0) = sumLimb w column limb+65536*carry w column limb := by
    dsimp [sumLimb,m]
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ _ (0 : F) _ _
    (ab 0) bb.1 (mb 0) (by decide +kernel) (carry_bounds localEffects column 0)
    (localEffects.bounds column 0).1 (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ _ _ _ _
    (ab 1) bb.2.1 (mb 1) (carry_bounds localEffects column 0) (carry_bounds localEffects column 1)
    (localEffects.bounds column 1).1 (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low
  rw [← bb.2.2]
  change Airbender.NativeWorkerFirstG.pack (sumLimb w column 0) (sumLimb w column 1) =
    Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerFirstG.sumLimb w column 0) (Airbender.NativeWorkerFirstG.sumLimb w column 1) +
      Airbender.NativeWorkerFirstG.pack (bInput w column 0) (bInput w column 1) + BitVec.ofNat 32 ((selected w m 0).val+65536*(selected w m 1).val)
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds column 0).1 (localEffects.bounds column 1).1,
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (ab 0) (ab 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ bb.1 bb.2.1]
  exact Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ _ _ _ _ _ _ low high

theorem chained_rotated {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    dAfter w column = (Airbender.NativeWorkerFirstG.dAfter w column ^^^
      Airbender.NativeWorkerFirstG.pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 8 := by
  rw [← Airbender.NativeWorkerCBProofs.d_pack effects column]
  exact rotated effects column

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerCB.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerSecondAD.RowEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have localEffects := mixing holds
  refine ⟨prior,localEffects,?_,carry_bounds localEffects,chained_rotated effects,addition prior effects localEffects⟩
  intro column limb
  have h := b_halves effects column
  fin_cases limb
  · exact h.1
  · exact h.2.1
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerSecondAD.RowEffects w := by
  have prior := Airbender.NativeWorkerCBProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerSecondADProofs
