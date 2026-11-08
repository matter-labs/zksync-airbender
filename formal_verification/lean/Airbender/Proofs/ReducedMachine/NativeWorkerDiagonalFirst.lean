import Airbender.Review.Circuits.Blake2Worker.DiagonalFirst
import Airbender.Proofs.ReducedMachine.NativeWorkerSecondCB

namespace Airbender.NativeWorkerDiagonalFirstProofs
open Airbender.Verification Airbender.NativeWorkerDiagonalFirst
open Airbender.NativeWorkerFirstG (pack)
open Airbender.Blake2Worker.Native
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
/-- Abstract canonical 9/7 packing, before native output sampling. -/
theorem pair97 (a lo hi : F) (lb : lo.val < 512) (hb : hi.val < 128)
    (same : a = lo+512*hi) :
    BitVec.ofNat 16 a.val = BitVec.append (BitVec.ofNat 7 hi.val) (BitVec.ofNat 9 lo.val) := by
  have bound : lo.val+512*hi.val < 65536 := by omega
  have cast : a = ((lo.val+512*hi.val : Nat) : F) := by simpa using same
  have canonical : a.val = lo.val+512*hi.val := by
    rw [cast,ZMod.val_natCast_of_lt (bound.trans (by decide +kernel))]
  apply BitVec.eq_of_toNat_eq
  change a.val%65536 = ((hi.val%128) <<< 9) ||| (lo.val%512)
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show lo.val%512 < 2^9 by omega)]
  simp [canonical,Nat.shiftLeft_eq,Nat.mod_eq_of_lt lb,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt bound,Nat.mul_comm]
  omega

@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_one : (2147483648 : F) = 1 := by decide +kernel
@[simp] private theorem coefficient_two : (4294967296 : F) = 2 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 16 := #v[
#v[(.var ⟨441⟩),(.var ⟨456⟩),(.var ⟨458⟩)],
#v[(.var ⟨442⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨155⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨171⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨236⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨238⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨252⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨290⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨293⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨294⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨357⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨358⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨452⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨453⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨456⟩))),(.var ⟨459⟩)],
#v[(.var ⟨443⟩),(.var ⟨457⟩),(.var ⟨460⟩)],
#v[(.var ⟨440⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨157⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨173⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨237⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨239⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨253⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨270⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨271⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨288⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨289⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨295⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨296⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨297⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨298⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨299⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨356⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨359⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨452⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨453⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨454⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨455⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨457⟩))),(.var ⟨461⟩)],
#v[(.var ⟨303⟩),(.var ⟨500⟩),(.var ⟨502⟩)],
#v[(.var ⟨304⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨159⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨175⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨240⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨242⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨256⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨336⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨339⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨340⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨403⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨404⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨496⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨497⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨500⟩))),(.var ⟨503⟩)],
#v[(.var ⟨305⟩),(.var ⟨501⟩),(.var ⟨504⟩)],
#v[(.var ⟨302⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨161⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨177⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨241⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨243⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨257⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨316⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨317⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨334⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨335⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨341⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨342⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨343⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨344⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨345⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨402⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨405⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨496⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨497⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨498⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨499⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨501⟩))),(.var ⟨505⟩)],
#v[(.var ⟨349⟩),(.var ⟨544⟩),(.var ⟨546⟩)],
#v[(.var ⟨350⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨163⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨179⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨244⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨246⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨260⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨382⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨385⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨386⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨449⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨450⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨540⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨541⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨544⟩))),(.var ⟨547⟩)],
#v[(.var ⟨351⟩),(.var ⟨545⟩),(.var ⟨548⟩)],
#v[(.var ⟨348⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨165⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨181⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨245⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨247⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨261⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨362⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨363⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨380⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨381⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨387⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨388⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨389⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨390⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨391⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨448⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨451⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨540⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨541⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨542⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨543⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨545⟩))),(.var ⟨549⟩)],
#v[(.var ⟨395⟩),(.var ⟨588⟩),(.var ⟨590⟩)],
#v[(.var ⟨396⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨167⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨183⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨248⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨250⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨264⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨311⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨312⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨428⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨431⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨432⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨584⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨585⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨588⟩))),(.var ⟨591⟩)],
#v[(.var ⟨397⟩),(.var ⟨589⟩),(.var ⟨592⟩)],
#v[(.var ⟨394⟩),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨169⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨185⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨249⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨251⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨265⟩))) (.mul (.mul (.const (1 : F)) (.const (2 : F))) (.var ⟨310⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨313⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨408⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨409⟩))) (.mul (.mul (.const (1 : F)) (.const (134217728 : F))) (.var ⟨426⟩))) (.mul (.mul (.const (1 : F)) (.const (-1073741823 : F))) (.var ⟨427⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨433⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨434⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨435⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨436⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨437⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨584⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨585⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨586⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨587⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨589⟩))),(.var ⟨593⟩)]]

/-- Exact actual query syntax is bound BEFORE witness evaluation. -/
private theorem shape (diagonal : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨72+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
    sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  fin_cases diagonal <;> fin_cases piece <;> fin_cases entry <;> rfl
private theorem value (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (query w diagonal piece)[entry.val]'(by have := entry.isLt; omega) =
    Expression.eval (environment w) sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][entry] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece entry)

private theorem value0 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[0] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][0] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 0)

private theorem value1 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[1] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][1] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 1)

private theorem value2 (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[2] = Expression.eval (environment w)
      sourceExpressions[(⟨4*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩ : Fin 16)][2] := by
  simpa [query,fixedQuery] using congrArg (Expression.eval (environment w)) (shape diagonal piece 2)

private theorem sum_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    sumLimb w diagonal limb = (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[1] +
      256*(query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[1] := by
  rw [value1 w diagonal _,value1 w diagonal _]
  fin_cases diagonal <;> fin_cases limb
  all_goals
    simp [sumLimb,inputLimb,columnLimb,sourceColumn,bLimb,carry,
      Airbender.NativeWorkerSecondAD.sumLimb,Airbender.NativeWorkerSecondAD.bInput,Airbender.NativeWorkerSecondAD.carry,
      Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,
      Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns,
      Airbender.NativeWorkerSchedule.selected,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem d_reconstruction (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) :
    inputLimb w diagonal 3 limb = (query w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩)[0] +
      256*(query w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w diagonal _,value0 w diagonal _]
  fin_cases diagonal <;> fin_cases limb <;>
    simp [inputLimb,columnLimb,sourceColumn,Airbender.NativeWorkerSecondCB.dLimb,
      Airbender.NativeWorkerSecondCB.dByte,sourceExpressions,Expression.eval,environment]
private theorem block0 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock0 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock0 setup).Sublist ([] ++ constraintsBlock0 setup) := by
    simp
  exact ((((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


private theorem block1 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock1 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock1 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup) := List.sublist_append_right _ _
  exact (((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private def booleanSyntax (column : Nat) : Expression F :=
  .add (.add (.const 0) (.add (.add (.const 0) (.const 0))
    (.mul (.mul (.const 1) (.const (-1))) (.var ⟨column⟩))))
    (.mul (.mul (.mul (.const 1) (.const 1)) (.var ⟨column⟩)) (.var ⟨column⟩))
private theorem bit0_shape (setup : Table F (fields 4)) (diagonal slot : Fin 4)
    (cut : 61+12*diagonal.val+slot.val < 64) :
    (FlatOperation.constraints (constraintsBlock0 setup)).get
      ⟨61+12*diagonal.val+slot.val,by change 61+12*diagonal.val+slot.val < 64; exact cut⟩ =
      booleanSyntax (452+44*diagonal.val+slot.val) := by
  fin_cases diagonal <;> fin_cases slot <;> norm_num at cut
  all_goals rfl
private theorem bit1_shape (setup : Table F (fields 4)) (diagonal slot : Fin 4)
    (cut : 64 ≤ 61+12*diagonal.val+slot.val) :
    (FlatOperation.constraints (constraintsBlock1 setup)).get
      ⟨61+12*diagonal.val+slot.val-64,by change 61+12*diagonal.val+slot.val-64 < 64; have := diagonal.isLt; have := slot.isLt; omega⟩ =
      booleanSyntax (452+44*diagonal.val+slot.val) := by
  fin_cases diagonal <;> fin_cases slot <;> norm_num at cut
  all_goals rfl

theorem carry_bits {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (diagonal slot : Fin 4) : (carryBit w diagonal slot).val ≤ 1 := by
  have bit : Expression.eval (environment w) (booleanSyntax (452+44*diagonal.val+slot.val)) = 0 := by
    by_cases cut : 61+12*diagonal.val+slot.val < 64
    · have h := assertion_of_holds (block0 holds)
        ⟨61+12*diagonal.val+slot.val,by change 61+12*diagonal.val+slot.val < 64; exact cut⟩
      rwa [bit0_shape setup diagonal slot cut] at h
    · have h := assertion_of_holds (block1 holds)
        ⟨61+12*diagonal.val+slot.val-64,by change 61+12*diagonal.val+slot.val-64 < 64; have := diagonal.isLt; have := slot.isLt; omega⟩
      rwa [bit1_shape setup diagonal slot (by omega)] at h
  simp [booleanSyntax,Expression.eval,environment] at bit
  obtain ⟨n,bound,same⟩ := Airbender.Arithmetic.boolean_nat (by linear_combination bit)
  change (w (452+44*diagonal.val+slot.val)).val ≤ 1
  rw [same]
  simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

private theorem byte_effects {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[0].val < 256 ∧ (query w diagonal piece)[1].val < 256 ∧
    (query w diagonal piece)[2].val < 256 ∧
    (query w diagonal piece)[2].val = (query w diagonal piece)[0].val ^^^ (query w diagonal piece)[1].val := by
  let slot : Fin 208 := ⟨72+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases diagonal <;> fin_cases piece <;> norm_num [fixedKind]
  exact ⟨by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.leftBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.rightBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.outputBounds slot,
    effects.results slot⟩

private theorem output_value (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) :
    (query w diagonal piece)[2] = w (458+44*diagonal.val+piece.val) := by
  rw [value2 w diagonal piece]
  fin_cases diagonal <;> fin_cases piece <;> simp [sourceExpressions,Expression.eval,environment]

theorem limb_bounds {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (sumLimb w diagonal limb).val < 65536 := by
  have low := byte_effects effects diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := byte_effects effects diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  rw [sum_reconstruction]
  exact Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 256 (by omega)

private theorem xor_bytes (a b c d : BitVec 8) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append
private theorem xor_halves (a b c d : BitVec 16) :
    (BitVec.append a b ^^^ BitVec.append c d) = BitVec.append (a ^^^ c) (b ^^^ d) := BitVec.xor_append

private theorem half_xor {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (BitVec.ofNat 16 (inputLimb w diagonal 3 limb).val ^^^ BitVec.ofNat 16 (sumLimb w diagonal limb).val) =
    BitVec.append (byte w diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩)
      (byte w diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩) := by
  let low : Fin 4 := ⟨2*limb.val,by have := limb.isLt; omega⟩
  let high : Fin 4 := ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  have l := byte_effects effects diagonal low
  have h := byte_effects effects diagonal high
  have d := Airbender.NativeWorkerFirstGProofs.pair_bytes (inputLimb w diagonal 3 limb) _ _ l.1 h.1 (d_reconstruction w diagonal limb)
  have a := Airbender.NativeWorkerFirstGProofs.pair_bytes (sumLimb w diagonal limb) _ _ l.2.1 h.2.1 (sum_reconstruction w diagonal limb)
  have out0 := Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ l.1 l.2.1 l.2.2.1 l.2.2.2
  have out1 := Airbender.NativeWorkerFirstGProofs.byte_xor _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2
  rw [output_value] at out0 out1
  rw [d,a,xor_bytes,← out0,← out1]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (diagonal : Fin 4) :
    dAfter w diagonal = (inputWord w diagonal 3 ^^^ aAfter w diagonal).rotateRight 16 := by
  unfold dAfter inputWord aAfter pack
  rw [xor_halves,half_xor effects,half_xor effects,Airbender.NativeWorkerFirstGProofs.rotate16]
  norm_num
  congr 3

/-- Exact previous B outputs; no table or output-equivalence assumption. -/
private theorem b_shape (column piece : Fin 4) :
    (fixedExpressions ⟨14+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[2] =
      .var ⟨310+46*column.val+piece.val⟩ := by
  fin_cases column <;> fin_cases piece <;> rfl
private def bWidth (piece : Fin 4) : Nat := #v[7,9,7,9][piece]
private theorem b_chunk_bounds {w : Nat → F} (effects : LookupEffects w) (column piece : Fin 4) :
    (w (310+46*column.val+piece.val)).val < 2^bWidth piece := by
  let slot : Fin 208 := ⟨14+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
  have kind : (fixedKind slot).bound = 2^bWidth piece := by
    dsimp only [slot]
    fin_cases column <;> fin_cases piece <;> norm_num [fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound,bWidth]
  have same : (fixedQuery w slot)[2] = w (310+46*column.val+piece.val) := by
    simpa [fixedQuery,slot,Expression.eval,environment] using congrArg (Expression.eval (environment w)) (b_shape column piece)
  have h := effects.outputBounds slot
  rwa [same,kind] at h

theorem b_halves {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    (bLimb w column 0).val < 65536 ∧ (bLimb w column 1).val < 65536 ∧
      pack (bLimb w column 0) (bLimb w column 1) = Airbender.NativeWorkerSecondCB.bAfter w column := by
  have b0 : (w (310+46*column.val)).val < 128 := b_chunk_bounds effects column 0
  have b1 : (w (311+46*column.val)).val < 512 := by
    have h : (w (310+46*column.val+1)).val < 512 := b_chunk_bounds effects column 1
    rwa [show 310+46*column.val+1=311+46*column.val by omega] at h
  have b2 : (w (312+46*column.val)).val < 128 := by
    have h : (w (310+46*column.val+2)).val < 128 := b_chunk_bounds effects column 2
    rwa [show 310+46*column.val+2=312+46*column.val by omega] at h
  have b3 : (w (313+46*column.val)).val < 512 := by
    have h : (w (310+46*column.val+3)).val < 512 := b_chunk_bounds effects column 3
    rwa [show 310+46*column.val+3=313+46*column.val by omega] at h
  have low := pair97 (w (311+46*column.val)+512*w (312+46*column.val)) _ _ b1 b2 rfl
  have high := pair97 (w (313+46*column.val)+512*w (310+46*column.val)) _ _ b3 b0 rfl
  refine ⟨Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 512 (by omega),
    Airbender.NativeWorkerWriteSliceProofs.reconstruct _ _ 512 (by omega),?_⟩
  change BitVec.append (BitVec.ofNat 16 (w (313+46*column.val)+512*w (310+46*column.val)).val)
    (BitVec.ofNat 16 (w (311+46*column.val)+512*w (312+46*column.val)).val) = _
  rw [low,high]
  change BitVec.append (BitVec.append (BitVec.ofNat 7 (w (310+46*column.val)).val) (BitVec.ofNat 9 (w (313+46*column.val)).val))
    (BitVec.append (BitVec.ofNat 7 (w (312+46*column.val)).val) (BitVec.ofNat 9 (w (311+46*column.val)).val)) =
    BitVec.append (BitVec.append (BitVec.ofNat 7 (w (310+46*column.val)).val) (BitVec.ofNat 9 (w (311+46*column.val+2)).val))
      (BitVec.append (BitVec.ofNat 7 (w (310+46*column.val+2)).val) (BitVec.ofNat 9 (w (311+46*column.val)).val))
  rw [show 311+46*column.val+2=313+46*column.val by omega,show 310+46*column.val+2=312+46*column.val by omega]

theorem input_bounds {w : Nat → F} (prior : Airbender.NativeWorkerSecondCB.RowEffects w)
    (effects : LookupEffects w) (diagonal component : Fin 4) (limb : Fin 2) :
    (inputLimb w diagonal component limb).val < 65536 := by
  fin_cases component
  · exact (prior.prior.mixing.bounds (sourceColumn diagonal 0) limb).1
  · have b := b_halves effects (sourceColumn diagonal 1)
    fin_cases limb
    · exact b.1
    · exact b.2.1
  · exact prior.mixing.bounds (sourceColumn diagonal 2) limb
  · exact Airbender.NativeWorkerSecondCBProofs.d_bounds effects (sourceColumn diagonal 3) limb

theorem routed {w : Nat → F} (effects : LookupEffects w) (diagonal component : Fin 4) :
    inputWord w diagonal component = (Airbender.NativeWorkerSecondCB.columnResult w (sourceColumn diagonal component))[component] := by
  fin_cases component
  · rfl
  · exact (b_halves effects (sourceColumn diagonal 1)).2.2
  · rfl
  · exact Airbender.NativeWorkerSecondCBProofs.d_pack effects (sourceColumn diagonal 3)

theorem mixing {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨carry_bits holds,limb_bounds effects,rotated effects⟩

theorem carry_bounds {w : Nat → F} (effects : LocalEffects w) (diagonal : Fin 4) (limb : Fin 2) :
    (carry w diagonal limb).val ≤ 3 := by
  have b0 := effects.carries diagonal ⟨2*limb.val,by have := limb.isLt; omega⟩
  have b1 := effects.carries diagonal ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  change (w (452+44*diagonal.val+2*limb.val)).val ≤ 1 at b0
  change (w (452+44*diagonal.val+(2*limb.val+1))).val ≤ 1 at b1
  rw [show 452+44*diagonal.val+(2*limb.val+1)=453+44*diagonal.val+2*limb.val by omega] at b1
  exact (Airbender.NativeWorkerAdditionProofs.carry_value _ _ b0 b1).2

theorem addition {w : Nat → F} (prior : Airbender.NativeWorkerSecondCB.RowEffects w)
    (effects : LookupEffects w) (localEffects : LocalEffects w) (diagonal : Fin 4) :
    aAfter w diagonal = inputWord w diagonal 0+ inputWord w diagonal 1+
      Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩ := by
  let word : Fin 16 := ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩
  have selected (limb : Fin 2) : (Airbender.NativeWorkerSchedule.selected w word limb).val < 655360 := by
    have h := prior.prior.prior.prior.selected word limb
    omega
  have field (limb : Fin 2) : inputLimb w diagonal 0 limb+ inputLimb w diagonal 1 limb+
      Airbender.NativeWorkerSchedule.selected w word limb+(if limb.val=0 then 0 else carry w diagonal 0) =
      sumLimb w diagonal limb+65536*carry w diagonal limb := by
    unfold sumLimb
    dsimp only [word]
    ring
  have low := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ _ (0 : F) _ _
    (input_bounds prior effects diagonal 0 0) (input_bounds prior effects diagonal 1 0) (selected 0)
    (by decide +kernel) (carry_bounds localEffects diagonal 0) (localEffects.bounds diagonal 0) (by simpa using field 0)
  have high := Airbender.NativeWorkerAdditionProofs.limb_sum _ _ _ _ _ _
    (input_bounds prior effects diagonal 0 1) (input_bounds prior effects diagonal 1 1) (selected 1)
    (carry_bounds localEffects diagonal 0) (carry_bounds localEffects diagonal 1) (localEffects.bounds diagonal 1) (by simpa using field 1)
  simp only [ZMod.val_zero,Nat.add_zero] at low high
  unfold aAfter inputWord Airbender.NativeWorkerAddition.messageWord
  rw [Airbender.NativeWorkerAdditionProofs.pack_value _ _ (localEffects.bounds diagonal 0) (localEffects.bounds diagonal 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (input_bounds prior effects diagonal 0 0) (input_bounds prior effects diagonal 0 1),
    Airbender.NativeWorkerAdditionProofs.pack_value _ _ (input_bounds prior effects diagonal 1 0) (input_bounds prior effects diagonal 1 1)]
  exact Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ _ _ _ _ _ _ low high

theorem row {w : Nat → F} (prior : Airbender.NativeWorkerSecondCB.RowEffects w)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerDiagonalFirst.RowEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have localEffects := mixing holds
  exact ⟨prior,input_bounds prior effects,routed effects,localEffects,carry_bounds localEffects,addition prior effects localEffects⟩
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerDiagonalFirst.RowEffects w := by
  have prior := Airbender.NativeWorkerSecondCBProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior.1,fun w member => row (prior.2 w member) (processing w member).body⟩
end Airbender.NativeWorkerDiagonalFirstProofs
