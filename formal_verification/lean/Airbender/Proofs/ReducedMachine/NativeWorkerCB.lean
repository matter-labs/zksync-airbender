import Airbender.Review.Circuits.Blake2Worker.ColumnCB
import Airbender.Proofs.ReducedMachine.NativeWorkerAddition

namespace Airbender.NativeWorkerCBProofs
open Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem triple_value (a lo mid hi : F) (lb : lo.val < 8) (mb : mid.val < 512)
    (hb : hi.val < 16) (same : a = lo+8*mid+4096*hi) :
    a.val = lo.val+8*mid.val+4096*hi.val ∧ a.val < 65536 := by
  have small : lo.val+8*mid.val+4096*hi.val < 65536 := by omega
  have cast : a = ((lo.val+8*mid.val+4096*hi.val : Nat) : F) := by simpa using same
  rw [cast,ZMod.val_natCast_of_lt (small.trans (by decide +kernel))]
  exact ⟨rfl,small⟩

theorem triple_pack (a lo mid hi : F) (lb : lo.val < 8) (mb : mid.val < 512)
    (hb : hi.val < 16) (same : a = lo+8*mid+4096*hi) :
    BitVec.ofNat 16 a.val = BitVec.append (BitVec.ofNat 4 hi.val)
      (BitVec.append (BitVec.ofNat 9 mid.val) (BitVec.ofNat 3 lo.val)) := by
  have canonical := triple_value a lo mid hi lb mb hb same
  apply BitVec.eq_of_toNat_eq
  change a.val % 65536 = ((hi.val%16) <<< 12) ||| (((mid.val%512) <<< 3) ||| (lo.val%8))
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show lo.val%8 < 2^3 by omega)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show ((mid.val%512) <<< 3)+lo.val%8 < 2^12 by
    simp only [Nat.shiftLeft_eq]; omega)]
  simp [canonical.1,Nat.shiftLeft_eq,Nat.mod_eq_of_lt lb,Nat.mod_eq_of_lt mb,Nat.mod_eq_of_lt hb]
  omega

theorem piece_xor (width : Nat) (a b c : F) (ab : a.val < 2^width)
    (bb : b.val < 2^width) (cb : c.val < 2^width) (same : c.val = a.val ^^^ b.val) :
    BitVec.ofNat width c.val = (BitVec.ofNat width a.val ^^^ BitVec.ofNat width b.val) := by
  apply BitVec.eq_of_toNat_eq
  simpa [Nat.mod_eq_of_lt ab,Nat.mod_eq_of_lt bb,Nat.mod_eq_of_lt cb] using same

theorem rotate12 (l0 h0 : BitVec 3) (l1 h1 : BitVec 9) (l2 h2 : BitVec 4) :
    BitVec.append (BitVec.append (BitVec.append l1 l0) h2)
      (BitVec.append (BitVec.append h1 h0) l2) =
    (BitVec.append (BitVec.append h2 (BitVec.append h1 h0))
      (BitVec.append l2 (BitVec.append l1 l0))).rotateRight 12 := by
  have p12 (a : BitVec 9) (b : BitVec 3) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 3 then b.getLsbD j else a.getLsbD (j-3) := BitVec.getLsbD_append
  have p16l (a : BitVec 12) (b : BitVec 4) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 4 then b.getLsbD j else a.getLsbD (j-4) := BitVec.getLsbD_append
  have p16r (a : BitVec 4) (b : BitVec 12) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 12 then b.getLsbD j else a.getLsbD (j-12) := BitVec.getLsbD_append
  have p32 (a b : BitVec 16) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 16 then b.getLsbD j else a.getLsbD (j-16) := BitVec.getLsbD_append
  have rot (x : BitVec 32) (j : Nat) (bound : j < 32) :
      (x.rotateRight 12).getLsbD j = if j < 20 then x.getLsbD (12+j) else x.getLsbD (j-20) := by
    rw [BitVec.getLsbD_rotateRight_of_lt (by decide +kernel)]
    by_cases cut : j < 20
    · simp [cut]
    · simp [cut,bound]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  rw [rot _ _ (by omega)]
  simp only [p32,p16l,p16r,p12]
  split_ifs <;> congr 1 <;> omega

open Airbender.NativeWorkerCB Airbender.NativeWorkerInitial Airbender.Blake2Worker.Native
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient8 : (17179869176 : F) = 0 := by decide +kernel
@[simp] private theorem scale256 : (549755813888 : F) = 256 := by decide +kernel
@[simp] private theorem coefficient256 : (549755813632 : F) = 0 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 24 := #v[
#v[(.var ⟨286⟩),(.var ⟨282⟩),(.var ⟨288⟩)],
#v[(.var ⟨287⟩),(.var ⟨283⟩),(.var ⟨289⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨171⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨286⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨287⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨186⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨278⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨279⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨282⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨283⟩))),(.var ⟨290⟩)],
#v[(.var ⟨291⟩),(.var ⟨284⟩),(.var ⟨293⟩)],
#v[(.var ⟨292⟩),(.var ⟨285⟩),(.var ⟨294⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨173⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨291⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨292⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨187⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨275⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨276⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨281⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨284⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨285⟩))),(.var ⟨295⟩)],
#v[(.var ⟨332⟩),(.var ⟨328⟩),(.var ⟨334⟩)],
#v[(.var ⟨333⟩),(.var ⟨329⟩),(.var ⟨335⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨175⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨332⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨333⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨188⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨324⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨325⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨328⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨329⟩))),(.var ⟨336⟩)],
#v[(.var ⟨337⟩),(.var ⟨330⟩),(.var ⟨339⟩)],
#v[(.var ⟨338⟩),(.var ⟨331⟩),(.var ⟨340⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨177⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨337⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨338⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨189⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨321⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨322⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨327⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨330⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨331⟩))),(.var ⟨341⟩)],
#v[(.var ⟨378⟩),(.var ⟨374⟩),(.var ⟨380⟩)],
#v[(.var ⟨379⟩),(.var ⟨375⟩),(.var ⟨381⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨179⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨378⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨379⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨190⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨370⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨371⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨374⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨375⟩))),(.var ⟨382⟩)],
#v[(.var ⟨383⟩),(.var ⟨376⟩),(.var ⟨385⟩)],
#v[(.var ⟨384⟩),(.var ⟨377⟩),(.var ⟨386⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨181⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨383⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨384⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨191⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨367⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨368⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨373⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨376⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨377⟩))),(.var ⟨387⟩)],
#v[(.var ⟨424⟩),(.var ⟨420⟩),(.var ⟨426⟩)],
#v[(.var ⟨425⟩),(.var ⟨421⟩),(.var ⟨427⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨183⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨424⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨425⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨192⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨416⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨417⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨420⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨421⟩))),(.var ⟨428⟩)],
#v[(.var ⟨429⟩),(.var ⟨422⟩),(.var ⟨431⟩)],
#v[(.var ⟨430⟩),(.var ⟨423⟩),(.var ⟨432⟩)],
#v[(.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨185⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨429⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨430⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨193⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨413⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨414⟩))) (.mul (.mul (.const (1 : F)) (.const (524288 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (-16 : F))) (.var ⟨419⟩))) (.mul (.mul (.const (1 : F)) (.const (-524288 : F))) (.var ⟨422⟩))) (.mul (.mul (.const (1 : F)) (.const (-4194304 : F))) (.var ⟨423⟩))),(.var ⟨433⟩)]]
/-- All actual three-field source bindings precede witness evaluation. -/
private theorem shape (column : Fin 4) (piece : Fin 6) (entry : Fin 3) :
    (fixedExpressions ⟨4+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
    sourceExpressions[(⟨6*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 24)][entry] := by
  fin_cases column <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value0 (w : Nat → F) (column : Fin 4) (piece : Fin 6) :
    (query w column piece)[0] = Expression.eval (environment w)
      sourceExpressions[(⟨6*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 24)][0] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece 0)
private theorem value1 (w : Nat → F) (column : Fin 4) (piece : Fin 6) :
    (query w column piece)[1] = Expression.eval (environment w)
      sourceExpressions[(⟨6*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 24)][1] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece 1)
private theorem value2 (w : Nat → F) (column : Fin 4) (piece : Fin 6) :
    (query w column piece)[2] = Expression.eval (environment w)
      sourceExpressions[(⟨6*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Fin 24)][2] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape column piece 2)
private theorem cLimb_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    cLimb w column limb = (query w column ⟨3*limb.val,by have := limb.isLt; omega⟩)[1] +
      8*(query w column ⟨3*limb.val+1,by have := limb.isLt; omega⟩)[1] +
      4096*(query w column ⟨3*limb.val+2,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w column _,value1 w column _,value1 w column _]
  fin_cases column <;> fin_cases limb
  all_goals
    simp [cLimb,cInput,dLimb,dByte,carry,observed,initialColumns,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem bInput_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    bInput w column limb = (query w column ⟨3*limb.val,by have := limb.isLt; omega⟩)[0] +
      8*(query w column ⟨3*limb.val+1,by have := limb.isLt; omega⟩)[0] +
      4096*(query w column ⟨3*limb.val+2,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w column _,value0 w column _,value0 w column _]
  fin_cases column <;> fin_cases limb
  all_goals
    simp [bInput,observed,initialColumns,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
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
    (column : Fin 4) (limb : Fin 2) : (carry w column limb).val ≤ 1 := by
  have bit := assertion_of_holds (block0 holds) ⟨17+12*column.val+limb.val,by change 17+12*column.val+limb.val < 64; have := column.isLt; have := limb.isLt; omega⟩
  fin_cases column <;> fin_cases limb
  all_goals
    simp [constraintsBlock0,FlatOperation.constraints,Expression.eval,environment,carry] at bit ⊢
    obtain ⟨n,bound,same⟩ := Airbender.Arithmetic.boolean_nat (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

private def width (piece : Fin 3) : Nat := #v[3,9,4][piece]
private theorem query_effects {w : Nat → F} (effects : LookupEffects w)
    (column : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val < 2^width piece ∧
    (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val < 2^width piece ∧
    (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val < 2^width piece ∧
    (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val =
      (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val ^^^
      (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val := by
  let slot : Fin 208 := ⟨4+18*column.val+(3*limb.val+piece.val),by have := column.isLt; have := limb.isLt; have := piece.isLt; omega⟩
  have bound : (fixedKind slot).bound = 2^width piece := by
    dsimp only [slot]
    fin_cases column <;> fin_cases limb <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound,width]
  exact ⟨by simpa only [bound,query,slot] using effects.leftBounds slot,
    by simpa only [bound,query,slot] using effects.rightBounds slot,
    by simpa only [bound,query,slot] using effects.outputBounds slot,effects.results slot⟩

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (cLimb w column limb).val < 65536 ∧ (bInput w column limb).val < 65536 := by
  have lo := query_effects effects column limb 0
  have mid := query_effects effects column limb 1
  have hi := query_effects effects column limb 2
  constructor
  · exact (triple_value _ _ _ _ lo.2.1 mid.2.1 hi.2.1 (cLimb_reconstruction w column limb)).2
  · exact (triple_value _ _ _ _ lo.1 mid.1 hi.1 (bInput_reconstruction w column limb)).2

private theorem output_value (w : Nat → F) (column : Fin 4) (limb : Fin 2) (piece : Fin 3) :
    (query w column ⟨3*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2] = w (288+46*column.val+5*limb.val+piece.val) := by
  rw [value2]
  fin_cases column <;> fin_cases limb <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]

private theorem xor3 (a c : BitVec 4) (b d : BitVec 12) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor12 (a c : BitVec 9) (b d : BitVec 3) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor32 (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (bInput w column limb).val ^^^ BitVec.ofNat 16 (cLimb w column limb).val) =
      BitVec.append (chunk4 w column limb) (BitVec.append (chunk9 w column limb) (chunk3 w column limb)) := by
  have lo := query_effects effects column limb 0
  have mid := query_effects effects column limb 1
  have hi := query_effects effects column limb 2
  have b := triple_pack _ _ _ _ lo.1 mid.1 hi.1 (bInput_reconstruction w column limb)
  have c := triple_pack _ _ _ _ lo.2.1 mid.2.1 hi.2.1 (cLimb_reconstruction w column limb)
  have x0 := piece_xor 3 _ _ _ lo.1 lo.2.1 lo.2.2.1 lo.2.2.2
  have x1 := piece_xor 9 _ _ _ mid.1 mid.2.1 mid.2.2.1 mid.2.2.2
  have x2 := piece_xor 4 _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  let q0 := query w column (⟨3*limb.val,by have := limb.isLt; omega⟩ : Fin 6)
  let q1 := query w column (⟨3*limb.val+1,by have := limb.isLt; omega⟩ : Fin 6)
  let q2 := query w column (⟨3*limb.val+2,by have := limb.isLt; omega⟩ : Fin 6)
  change BitVec.ofNat 16 (bInput w column limb).val = BitVec.append (BitVec.ofNat 4 q2[0].val)
    (BitVec.append (BitVec.ofNat 9 q1[0].val) (BitVec.ofNat 3 q0[0].val)) at b
  change BitVec.ofNat 16 (cLimb w column limb).val = BitVec.append (BitVec.ofNat 4 q2[1].val)
    (BitVec.append (BitVec.ofNat 9 q1[1].val) (BitVec.ofNat 3 q0[1].val)) at c
  rw [output_value] at x0 x1 x2
  change BitVec.ofNat 3 (w (288+46*column.val+5*limb.val)).val =
    (BitVec.ofNat 3 q0[0].val ^^^ BitVec.ofNat 3 q0[1].val) at x0
  change BitVec.ofNat 9 (w (288+46*column.val+5*limb.val+1)).val =
    (BitVec.ofNat 9 q1[0].val ^^^ BitVec.ofNat 9 q1[1].val) at x1
  change BitVec.ofNat 4 (w (288+46*column.val+5*limb.val+2)).val =
    (BitVec.ofNat 4 q2[0].val ^^^ BitVec.ofNat 4 q2[1].val) at x2
  rw [show 288+46*column.val+5*limb.val+1 = 289+46*column.val+5*limb.val by omega] at x1
  rw [show 288+46*column.val+5*limb.val+2 = 290+46*column.val+5*limb.val by omega] at x2
  rw [b,c,xor3,xor12,← x0,← x1,← x2]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    bAfter w column = (Airbender.NativeWorkerFirstG.pack (bInput w column 0) (bInput w column 1) ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1)).rotateRight 12 := by
  unfold bAfter Airbender.NativeWorkerFirstG.pack
  rw [xor32,half_xor effects,half_xor effects,← rotate12]
/-- Exact original byte-query output syntax before its witness evaluation. -/
private theorem d_shape (column : Fin 4) (piece : Fin 4) :
    (fixedExpressions ⟨18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨275+46*column.val+piece.val+piece.val/2⟩ := by
  fin_cases column <;> fin_cases piece <;> rfl
private theorem d_byte_bounds {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (piece : Fin 4) :
    (dByte w column piece).val < 256 := by
  let slot : Fin 208 := ⟨18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases column <;> fin_cases piece <;> norm_num [fixedKind]
  have same : (fixedQuery w slot)[2] = dByte w column piece := by
    simpa [fixedQuery,dByte,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (d_shape column piece)
  have bound := effects.outputBounds slot
  rw [same] at bound
  simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound] using bound

theorem d_bounds {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (dLimb w column limb).val < 65536 := by
  have b0 := d_byte_bounds effects column 0
  have b1 := d_byte_bounds effects column 1
  have b2 := d_byte_bounds effects column 2
  have b3 := d_byte_bounds effects column 3
  fin_cases limb
  · exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)
  · exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)

theorem d_pack {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (dLimb w column 0) (dLimb w column 1) =
      Airbender.NativeWorkerFirstG.dAfter w column := by
  have low := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w column 2+256*dByte w column 3) _ _ (d_byte_bounds effects column 2) (d_byte_bounds effects column 3) rfl
  have high := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w column 0+256*dByte w column 1) _ _ (d_byte_bounds effects column 0) (d_byte_bounds effects column 1) rfl
  change BitVec.append (BitVec.ofNat 16 (dByte w column 0+256*dByte w column 1).val)
    (BitVec.ofNat 16 (dByte w column 2+256*dByte w column 3).val) = _
  rw [low,high]
  rfl

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerAddition.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (column : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1) =
      Airbender.NativeWorkerAddition.preGWord w ⟨8+column.val,by have := column.isLt; omega⟩ +
        Airbender.NativeWorkerFirstG.dAfter w column := by
  have cb (limb : Fin 2) : (cInput w column limb).val < 65536 := prior.initial _ limb
  have field (limb : Fin 2) : cInput w column limb + dLimb w column limb + (0 : F) +
      (if limb.val = 0 then 0 else carry w column 0) = cLimb w column limb+65536*carry w column limb := by
    unfold cLimb
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) (0 : F) _ _
    (cb 0) (d_bounds effects column 0) (by decide +kernel) (by decide +kernel)
    ((localEffects.carries column 0).trans (by decide +kernel)) (localEffects.bounds column 0).1 (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) _ _ _
    (cb 1) (d_bounds effects column 1) (by decide +kernel)
    ((localEffects.carries column 0).trans (by decide +kernel)) ((localEffects.carries column 1).trans (by decide +kernel))
    (localEffects.bounds column 1).1 (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low high
  rw [← d_pack effects column]
  change Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1) =
    Airbender.NativeWorkerFirstG.pack (cInput w column 0) (cInput w column 1) +
      Airbender.NativeWorkerFirstG.pack (dLimb w column 0) (dLimb w column 1)
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds column 0).1 (localEffects.bounds column 1).1,
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (cb 0) (cb 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (d_bounds effects column 0) (d_bounds effects column 1)]
  simpa using Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ 0 0 _ _ _ _ low high

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerAddition.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerCB.RowEffects w := by
  have localEffects := mixing holds
  exact ⟨prior,localEffects,addition prior (Airbender.Blake2Worker.QueryProofs.lookup_effects holds) localEffects⟩
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerCB.RowEffects w := by
  have prior := Airbender.NativeWorkerAdditionProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerCBProofs
