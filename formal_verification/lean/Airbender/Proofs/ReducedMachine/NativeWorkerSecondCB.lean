import Airbender.Review.Circuits.Blake2Worker.SecondCB
import Airbender.Proofs.ReducedMachine.NativeWorkerSecondAD

namespace Airbender.NativeWorkerSecondCBProofs
open Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem pair_pack (a lo hi : F) (lb : lo.val < 128) (hb : hi.val < 512)
    (same : a = lo+128*hi) :
    BitVec.ofNat 16 a.val = BitVec.append (BitVec.ofNat 9 hi.val) (BitVec.ofNat 7 lo.val) := by
  have bound : lo.val+128*hi.val < 65536 := by omega
  have cast : a = ((lo.val+128*hi.val : Nat) : F) := by simpa using same
  have canonical : a.val = lo.val+128*hi.val := by
    rw [cast,ZMod.val_natCast_of_lt (bound.trans (by decide +kernel))]
  apply BitVec.eq_of_toNat_eq
  change a.val%65536 = ((hi.val%512) <<< 7) ||| (lo.val%128)
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show lo.val%128 < 2^7 by omega)]
  simp [canonical,Nat.shiftLeft_eq,Nat.mod_eq_of_lt lb,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt bound,Nat.mul_comm]
  omega

theorem rotate7 (l0 h0 : BitVec 7) (l1 h1 : BitVec 9) :
    BitVec.append (BitVec.append l0 h1) (BitVec.append h0 l1) =
      (BitVec.append (BitVec.append h1 h0) (BitVec.append l1 l0)).rotateRight 7 := by
  have p16l (a : BitVec 7) (b : BitVec 9) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 9 then b.getLsbD j else a.getLsbD (j-9) := BitVec.getLsbD_append
  have p16r (a : BitVec 9) (b : BitVec 7) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 7 then b.getLsbD j else a.getLsbD (j-7) := BitVec.getLsbD_append
  have p32 (a b : BitVec 16) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 16 then b.getLsbD j else a.getLsbD (j-16) := BitVec.getLsbD_append
  have rot (x : BitVec 32) (j : Nat) (bound : j < 32) :
      (x.rotateRight 7).getLsbD j = if j < 25 then x.getLsbD (7+j) else x.getLsbD (j-25) := by
    rw [BitVec.getLsbD_rotateRight_of_lt (by decide +kernel)]
    by_cases cut : j < 25
    · simp [cut]
    · simp [cut,bound]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  rw [rot _ _ (by omega)]
  simp only [p32,p16l,p16r]
  split_ifs <;> congr 1 <;> omega

open Airbender.NativeWorkerSecondCB Airbender.NativeWorkerInitial Airbender.Blake2Worker.Native
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_one : (2147483648 : F) = 1 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 16 := #v[
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨290⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨293⟩))),(.var ⟨308⟩),(.var ⟨310⟩)],
#v[(.var ⟨294⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨186⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨278⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨279⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨303⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨304⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨308⟩))),(.var ⟨311⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨288⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨295⟩))),(.var ⟨309⟩),(.var ⟨312⟩)],
#v[(.var ⟨289⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨187⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨275⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨276⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨280⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨281⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨302⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨305⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨306⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨307⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨309⟩))),(.var ⟨313⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨336⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨339⟩))),(.var ⟨354⟩),(.var ⟨356⟩)],
#v[(.var ⟨340⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨188⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨324⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨325⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨349⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨350⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨354⟩))),(.var ⟨357⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨334⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨341⟩))),(.var ⟨355⟩),(.var ⟨358⟩)],
#v[(.var ⟨335⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨189⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨321⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨322⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨326⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨327⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨348⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨351⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨352⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨353⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨355⟩))),(.var ⟨359⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨382⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨385⟩))),(.var ⟨400⟩),(.var ⟨402⟩)],
#v[(.var ⟨386⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨190⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨370⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨371⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨395⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨396⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨400⟩))),(.var ⟨403⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨380⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨387⟩))),(.var ⟨401⟩),(.var ⟨404⟩)],
#v[(.var ⟨381⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨191⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨367⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨368⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨372⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨373⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨394⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨397⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨398⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨399⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨401⟩))),(.var ⟨405⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨428⟩))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨431⟩))),(.var ⟨446⟩),(.var ⟨448⟩)],
#v[(.var ⟨432⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨192⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨416⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨417⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨441⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨442⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨446⟩))),(.var ⟨449⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16 : F))) (.var ⟨426⟩))) (.mul (.mul (.const (1 : F)) (.const (1 : F))) (.var ⟨433⟩))),(.var ⟨447⟩),(.var ⟨450⟩)],
#v[(.var ⟨427⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨193⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨413⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨414⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨418⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨419⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨440⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨443⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨444⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨445⟩))) (.mul (.mul (.const (1 : F)) (.const (-16777216 : F))) (.var ⟨447⟩))),(.var ⟨451⟩)]]

/-- Exact actual query syntax is bound BEFORE witness evaluation. -/
private theorem shape (column : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨14+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
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


private theorem c_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    cLimb w column limb = (query w column ⟨2*limb.val,by have := limb.isLt; omega⟩)[1] +
      128*(query w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w column _,value1 w column _]
  fin_cases column <;> fin_cases limb
  all_goals
    simp [cLimb,cInput,dLimb,dByte,carry,Airbender.NativeWorkerCB.cLimb,
      Airbender.NativeWorkerCB.cInput,Airbender.NativeWorkerCB.dLimb,
      Airbender.NativeWorkerCB.dByte,Airbender.NativeWorkerCB.carry,
      observed,initialColumns,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem b_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    bInput w column limb = (query w column ⟨2*limb.val,by have := limb.isLt; omega⟩)[0] +
      128*(query w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w column _,value0 w column _]
  fin_cases column <;> fin_cases limb <;>
    simp [bInput,Airbender.NativeWorkerSecondAD.bInput,sourceExpressions,Expression.eval,environment] <;> ring
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
  have bit := assertion_of_holds (block0 holds) ⟨23+12*column.val+limb.val,by change 23+12*column.val+limb.val < 64; have := column.isLt; have := limb.isLt; omega⟩
  fin_cases column <;> fin_cases limb
  all_goals
    simp [constraintsBlock0,FlatOperation.constraints,Expression.eval,environment,carry] at bit ⊢
    obtain ⟨n,bound,same⟩ := Airbender.Arithmetic.boolean_nat (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound


private def width (piece : Fin 2) : Nat := #v[7,9][piece]
private theorem query_effects {w : Nat → F} (effects : LookupEffects w)
    (column : Fin 4) (limb : Fin 2) (piece : Fin 2) :
    (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val < 2^width piece ∧
    (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val < 2^width piece ∧
    (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val < 2^width piece ∧
    (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2].val =
      (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[0].val ^^^
      (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[1].val := by
  let slot : Fin 208 := ⟨14+18*column.val+(2*limb.val+piece.val),by have := column.isLt; have := limb.isLt; have := piece.isLt; omega⟩
  have bound : (fixedKind slot).bound = 2^width piece := by
    dsimp only [slot]
    fin_cases column <;> fin_cases limb <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound,width]
  exact ⟨by simpa only [bound,query,slot] using effects.leftBounds slot,
    by simpa only [bound,query,slot] using effects.rightBounds slot,
    by simpa only [bound,query,slot] using effects.outputBounds slot,effects.results slot⟩

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (cLimb w column limb).val < 65536 := by
  have lo := query_effects effects column limb 0
  have hi := query_effects effects column limb 1
  have lb : (query w column ⟨2*limb.val,by have := limb.isLt; omega⟩)[1].val < 128 := lo.2.1
  have hb : (query w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1].val < 512 := hi.2.1
  rw [c_reconstruction]
  exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 128 (by omega)

private theorem output_value (w : Nat → F) (column : Fin 4) (limb : Fin 2) (piece : Fin 2) :
    (query w column ⟨2*limb.val+piece.val,by have := limb.isLt; have := piece.isLt; omega⟩)[2] = w (310+46*column.val+2*limb.val+piece.val) := by
  rw [value2]
  fin_cases column <;> fin_cases limb <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]
private theorem xor16 (a c : BitVec 9) (b d : BitVec 7) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor32 (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (bInput w column limb).val ^^^ BitVec.ofNat 16 (cLimb w column limb).val) =
      BitVec.append (chunk9 w column limb) (chunk7 w column limb) := by
  have lo := query_effects effects column limb 0
  have hi := query_effects effects column limb 1
  have b := pair_pack _ _ _ lo.1 hi.1 (b_reconstruction w column limb)
  have c := pair_pack _ _ _ lo.2.1 hi.2.1 (c_reconstruction w column limb)
  have x0 := Airbender.NativeWorkerCBProofs.piece_xor 7 _ _ _ lo.1 lo.2.1 lo.2.2.1 lo.2.2.2
  have x1 := Airbender.NativeWorkerCBProofs.piece_xor 9 _ _ _ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  let q0 := query w column (⟨2*limb.val,by have := limb.isLt; omega⟩ : Fin 4)
  let q1 := query w column (⟨2*limb.val+1,by have := limb.isLt; omega⟩ : Fin 4)
  change BitVec.ofNat 16 (bInput w column limb).val = BitVec.append (BitVec.ofNat 9 q1[0].val) (BitVec.ofNat 7 q0[0].val) at b
  change BitVec.ofNat 16 (cLimb w column limb).val = BitVec.append (BitVec.ofNat 9 q1[1].val) (BitVec.ofNat 7 q0[1].val) at c
  rw [output_value] at x0 x1
  change BitVec.ofNat 7 (w (310+46*column.val+2*limb.val)).val =
    (BitVec.ofNat 7 q0[0].val ^^^ BitVec.ofNat 7 q0[1].val) at x0
  change BitVec.ofNat 9 (w (310+46*column.val+2*limb.val+1)).val =
    (BitVec.ofNat 9 q1[0].val ^^^ BitVec.ofNat 9 q1[1].val) at x1
  rw [show 310+46*column.val+2*limb.val+1 = 311+46*column.val+2*limb.val by omega] at x1
  rw [b,c,xor16,← x0,← x1]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    bAfter w column = (Airbender.NativeWorkerFirstG.pack (bInput w column 0) (bInput w column 1) ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1)).rotateRight 7 := by
  unfold bAfter Airbender.NativeWorkerFirstG.pack
  rw [xor32,half_xor effects,half_xor effects,← rotate7]



/-- Exact original second D-output syntax, before witness evaluation. -/
private theorem d_shape (column : Fin 4) (piece : Fin 4) :
    (fixedExpressions ⟨10+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨302+46*column.val+piece.val⟩ := by
  fin_cases column <;> fin_cases piece <;> rfl
private theorem d_byte_bounds {w : Nat → F} (effects : LookupEffects w)
    (column : Fin 4) (piece : Fin 4) : (dByte w column piece).val < 256 := by
  let slot : Fin 208 := ⟨10+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases column <;> fin_cases piece <;> norm_num [fixedKind]
  have same : (fixedQuery w slot)[2] = dByte w column piece := by
    simpa [fixedQuery,dByte,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (d_shape column piece)
  have h := effects.outputBounds slot
  rw [same] at h
  simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound] using h

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
    Airbender.NativeWorkerFirstG.pack (dLimb w column 0) (dLimb w column 1) = Airbender.NativeWorkerSecondAD.dAfter w column := by
  have low := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w column 1+256*dByte w column 2) _ _ (d_byte_bounds effects column 1) (d_byte_bounds effects column 2) rfl
  have high := Airbender.NativeWorkerFirstGProofs.pair_bytes
    (dByte w column 3+256*dByte w column 0) _ _ (d_byte_bounds effects column 3) (d_byte_bounds effects column 0) rfl
  change BitVec.append (BitVec.ofNat 16 (dByte w column 3+256*dByte w column 0).val)
    (BitVec.ofNat 16 (dByte w column 1+256*dByte w column 2).val) = _
  rw [low,high]
  rfl

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerSecondAD.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (column : Fin 4) :
    Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1) =
      Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerCB.cLimb w column 0) (Airbender.NativeWorkerCB.cLimb w column 1) +
        Airbender.NativeWorkerSecondAD.dAfter w column := by
  have cb (limb : Fin 2) : (cInput w column limb).val < 65536 := (prior.prior.mixing.bounds column limb).1
  have field (limb : Fin 2) : cInput w column limb+dLimb w column limb+(0 : F)+
      (if limb.val = 0 then 0 else carry w column 0) = cLimb w column limb+65536*carry w column limb := by
    unfold cLimb
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) (0 : F) _ _
    (cb 0) (d_bounds effects column 0) (by decide +kernel) (by decide +kernel)
    ((localEffects.carries column 0).trans (by decide +kernel)) (localEffects.bounds column 0) (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ (0 : F) _ _ _
    (cb 1) (d_bounds effects column 1) (by decide +kernel)
    ((localEffects.carries column 0).trans (by decide +kernel)) ((localEffects.carries column 1).trans (by decide +kernel))
    (localEffects.bounds column 1) (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low high
  rw [← d_pack effects column]
  change Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1) =
    Airbender.NativeWorkerFirstG.pack (cInput w column 0) (cInput w column 1) + Airbender.NativeWorkerFirstG.pack (dLimb w column 0) (dLimb w column 1)
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds column 0) (localEffects.bounds column 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (cb 0) (cb 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (d_bounds effects column 0) (d_bounds effects column 1)]
  simpa using Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ 0 0 _ _ _ _ low high

theorem chained_rotated {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    bAfter w column = (Airbender.NativeWorkerCB.bAfter w column ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1)).rotateRight 7 := by
  rw [← (Airbender.NativeWorkerSecondADProofs.b_halves effects column).2.2]
  exact rotated effects column

theorem column {w : Nat → F} (prior : Airbender.NativeWorkerSecondAD.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (column : Fin 4) :
    columnResult w column = g
      (Airbender.NativeWorkerAddition.preGWord w ⟨column.val,by have := column.isLt; omega⟩)
      (Airbender.NativeWorkerAddition.preGWord w ⟨4+column.val,by have := column.isLt; omega⟩)
      (Airbender.NativeWorkerAddition.preGWord w ⟨8+column.val,by have := column.isLt; omega⟩)
      (Airbender.NativeWorkerAddition.preGWord w ⟨12+column.val,by have := column.isLt; omega⟩)
      (Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val,by have := column.isLt; omega⟩)
      (Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val+1,by have := column.isLt; omega⟩) := by
  have a1 := prior.prior.prior.added column
  have d1 := prior.prior.prior.prior.rotated column
  have c1 := prior.prior.added column
  have b1 := prior.prior.mixing.rotated column
  have a2 := prior.added column
  have d2 := prior.chained column
  have c2 := addition prior effects localEffects column
  have b2 := chained_rotated effects column
  change Airbender.NativeWorkerFirstG.dAfter w column =
    (Airbender.NativeWorkerAddition.preGWord w ⟨12+column.val,by have := column.isLt; omega⟩ ^^^ Airbender.NativeWorkerAddition.aAfter w column).rotateRight 16 at d1
  change Airbender.NativeWorkerCB.bAfter w column =
    (Airbender.NativeWorkerAddition.preGWord w ⟨4+column.val,by have := column.isLt; omega⟩ ^^^
      Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerCB.cLimb w column 0) (Airbender.NativeWorkerCB.cLimb w column 1)).rotateRight 12 at b1
  simp only [columnResult,g,b2,c2,d2,a2,b1,c1,d1,a1]

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerSecondAD.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerSecondCB.RowEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have localEffects := mixing holds
  exact ⟨prior,localEffects,addition prior effects localEffects,chained_rotated effects,column prior effects localEffects⟩
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerSecondCB.RowEffects w := by
  have prior := Airbender.NativeWorkerSecondADProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerSecondCBProofs
