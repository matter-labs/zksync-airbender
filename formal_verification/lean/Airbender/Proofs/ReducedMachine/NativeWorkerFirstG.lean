import Airbender.Review.Circuits.Blake2Worker.FirstG
import Airbender.Proofs.ReducedMachine.NativeWorkerInitial
import Airbender.Proofs.Blake2Worker.NativeQueryResults

namespace Airbender.NativeWorkerFirstGProofs
open Airbender.Verification
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Entire abstract limb reconstruction BEFORE native query data. -/
theorem pair_bytes (a lo hi : F) (low : lo.val < 256) (high : hi.val < 256)
    (same : a = lo+256*hi) :
    BitVec.ofNat 16 a.val = BitVec.append (BitVec.ofNat 8 hi.val) (BitVec.ofNat 8 lo.val) := by
  have bound : lo.val+256*hi.val < 65536 := by omega
  have cast : a = ((lo.val+256*hi.val : Nat) : F) := by simpa using same
  have canonical : a.val = lo.val+256*hi.val := by
    rw [cast,ZMod.val_natCast_of_lt (show lo.val+256*hi.val < mersenne31Modulus by exact bound.trans (by decide +kernel))]
  apply BitVec.eq_of_toNat_eq
  change a.val % 65536 = ((hi.val % 256) <<< 8) ||| (lo.val % 256)
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show lo.val % 256 < 2^8 by omega)]
  simp [canonical,Nat.shiftLeft_eq,Nat.mod_eq_of_lt low,Nat.mod_eq_of_lt high,Nat.mod_eq_of_lt bound,Nat.mul_comm]
  omega

theorem byte_xor (a b c : F) (left : a.val < 256) (right : b.val < 256) (out : c.val < 256)
    (result : c.val = a.val ^^^ b.val) :
    BitVec.ofNat 8 c.val = (BitVec.ofNat 8 a.val ^^^ BitVec.ofNat 8 b.val) := by
  apply BitVec.eq_of_toNat_eq
  simpa [Nat.mod_eq_of_lt left,Nat.mod_eq_of_lt right,Nat.mod_eq_of_lt out] using result

theorem rotate16 (low high : BitVec 16) : (BitVec.append high low).rotateRight 16 = BitVec.append low high := by
  have append_bit (a b : BitVec 16) (j : Nat) :
      (BitVec.append a b).getLsbD j = if j < 16 then b.getLsbD j else a.getLsbD (j - 16) :=
    BitVec.getLsbD_append
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  rw [BitVec.getLsbD_rotateRight_of_lt (by decide +kernel)]
  simp only [append_bit,Nat.reduceAdd,Nat.reduceSub]
  by_cases small : i < 16
  · simp [small]
  · simp [small,show i < 32 by omega,show i - 16 < 16 by omega]

open Airbender.NativeWorkerFirstG Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
open Airbender.Blake2Worker.Native
@[simp] private theorem coefficient : (2147483647 : F) = 0 := by decide +kernel
@[simp] private theorem coefficient_one : (2147483648 : F) = 1 := by decide +kernel
@[simp] private theorem coefficient_two : (4294967296 : F) = 2 := by decide +kernel
private def sourceExpressions : Vector (Vector (Expression F) 3) 16 := #v[
#v[(.var ⟨274⟩),(.var ⟨272⟩),(.var ⟨275⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨198⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨274⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨155⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨171⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨236⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨272⟩))),(.var ⟨276⟩)],
#v[(.var ⟨277⟩),(.var ⟨273⟩),(.var ⟨278⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨199⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨277⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨157⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨173⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨237⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨268⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨269⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨270⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨271⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨273⟩))),(.var ⟨279⟩)],
#v[(.var ⟨320⟩),(.var ⟨318⟩),(.var ⟨321⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨194⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨320⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨159⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨175⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨240⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨318⟩))),(.var ⟨322⟩)],
#v[(.var ⟨323⟩),(.var ⟨319⟩),(.var ⟨324⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨195⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨323⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨161⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨177⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨241⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨314⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨315⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨316⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨317⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨319⟩))),(.var ⟨325⟩)],
#v[(.var ⟨366⟩),(.var ⟨364⟩),(.var ⟨367⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨200⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨366⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨163⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨179⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨244⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨364⟩))),(.var ⟨368⟩)],
#v[(.var ⟨369⟩),(.var ⟨365⟩),(.var ⟨370⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨201⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨369⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨165⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨181⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨245⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨360⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨361⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨362⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨363⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨365⟩))),(.var ⟨371⟩)],
#v[(.var ⟨412⟩),(.var ⟨410⟩),(.var ⟨413⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨196⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨412⟩))),(.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨167⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨183⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨248⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨410⟩))),(.var ⟨414⟩)],
#v[(.var ⟨415⟩),(.var ⟨411⟩),(.var ⟨416⟩)],
#v[(.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨197⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨415⟩))),(.add (.add (.add (.add (.add (.add (.add (.add (.add (.const (0 : F)) (.const (0 : F))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨169⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨185⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨249⟩))) (.mul (.mul (.const (1 : F)) (.const (8388608 : F))) (.var ⟨406⟩))) (.mul (.mul (.const (1 : F)) (.const (16777216 : F))) (.var ⟨407⟩))) (.mul (.mul (.const (1 : F)) (.const (-256 : F))) (.var ⟨408⟩))) (.mul (.mul (.const (1 : F)) (.const (-512 : F))) (.var ⟨409⟩))) (.mul (.mul (.const (1 : F)) (.const (-8388608 : F))) (.var ⟨411⟩))),(.var ⟨417⟩)]]

/-- Exact actual query syntax is bound BEFORE witness evaluation. -/
private theorem shape (column : Fin 4) (piece : Fin 4) (entry : Fin 3) :
    (fixedExpressions ⟨18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩ : Vector (Expression F) 4)[(⟨entry.val,by have := entry.isLt; omega⟩ : Fin 4)] =
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
    simp [sumLimb,carry,observed,initialColumns,selected,sourceExpressions,Expression.eval,environment]
    ring_nf
    simp
private theorem d_reconstruction (w : Nat → F) (column : Fin 4) (limb : Fin 2) :
    dInput w column limb = (query w column ⟨2*limb.val,by have := limb.isLt; omega⟩)[0] +
      256*(query w column ⟨2*limb.val+1,by have := limb.isLt; omega⟩)[0] := by
  rw [value0 w column _,value0 w column _]
  fin_cases column <;> fin_cases limb
  all_goals
    simp [dInput,observed,initialColumns,sourceExpressions,Expression.eval,environment]
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
    (column : Fin 4) (slot : Fin 4) : (carryBit w column slot).val ≤ 1 := by
  have bit := assertion_of_holds (block0 holds) ⟨13+12*column.val+slot.val,by change 13+12*column.val+slot.val < 64; have := column.isLt; have := slot.isLt; omega⟩
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
  let slot : Fin 208 := ⟨18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
  have kind : fixedKind slot = .byte := by
    dsimp only [slot]
    fin_cases column <;> fin_cases piece <;> norm_num [fixedKind]
  exact ⟨by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.leftBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.rightBounds slot,
    by simpa only [kind,Airbender.Blake2Worker.Fixed.Kind.bound,query,slot] using effects.outputBounds slot,
    effects.results slot⟩

private theorem output_value (w : Nat → F) (column : Fin 4) (piece : Fin 4) :
    (query w column piece)[2] = w (275+46*column.val+piece.val+piece.val/2) := by
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
  have d := pair_bytes (dInput w column limb) _ _ l.1 h.1 (d_reconstruction w column limb)
  have a := pair_bytes (sumLimb w column limb) _ _ l.2.1 h.2.1 (sum_reconstruction w column limb)
  have out0 := byte_xor _ _ _ l.1 l.2.1 l.2.2.1 l.2.2.2
  have out1 := byte_xor _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2
  rw [output_value] at out0 out1
  rw [d,a,xor_bytes,← out0,← out1]
  rfl

theorem rotated {w : Nat → F} (effects : LookupEffects w) (column : Fin 4) :
    dAfter w column = (pack (dInput w column 0) (dInput w column 1) ^^^
      pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 16 := by
  unfold dAfter pack
  rw [xor_halves,half_xor effects,half_xor effects,rotate16]
  norm_num
  congr 3

theorem row {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    Airbender.NativeWorkerFirstG.RowEffects w := by
  have effects := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  exact ⟨Airbender.NativeWorkerInitialProofs.row holds,carry_bits holds,limb_bounds effects,rotated effects⟩
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerFirstG.RowEffects w := by
  have prior := Airbender.NativeMixedReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  exact ⟨prior,fun w member => row (processing w member).body⟩
end Airbender.NativeWorkerFirstGProofs
