import Airbender.Review.Trace.Families.ReducedMachine.CallerCount
import Airbender.Proofs.ReducedMachine.NativeCallerValidity

namespace Airbender.NativeCallerCountProofs
open Airbender.NativeDelegationSupport Airbender.NativeCallerCount
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem count_bound {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K) :
    countAt rows key weight target ≤ rows.length := by
  induction rows with
  | nil => simp [countAt]
  | cons row rows ih =>
    simp only [countAt,List.map_cons,List.sum_cons,List.length_cons] at *
    split_ifs <;> omega

theorem count_cast {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K)
    (boolean : ∀ row ∈ rows, weight row = 0 ∨ weight row = 1) :
    (countAt rows key weight target : F) = weightAt rows key weight target := by
  induction rows with
  | nil => simp [countAt,weightAt]
  | cons row rows ih =>
    have rest : ∀ a ∈ rows, weight a = 0 ∨ weight a = 1 := fun a member => boolean a (by simp [member])
    have left : countAt (row::rows) key weight target =
        (if key row = target ∧ weight row = 1 then 1 else 0) + countAt rows key weight target := rfl
    have right : weightAt (row::rows) key weight target =
        (if key row = target then weight row else 0) + weightAt rows key weight target := by
      by_cases same : key row = target <;> simp [weightAt,same]
    rw [left,Nat.cast_add,ih rest,right]
    rcases boolean row (by simp) with zero | one
    · simp [zero]
    · simp [one]

theorem count_positive {A K : Type} [DecidableEq K] (rows : List A) (key : A → K) (weight : A → F) (target : K)
    (positive : 0 < countAt rows key weight target) :
    ∃ row ∈ rows, weight row = 1 ∧ key row = target := by
  induction rows with
  | nil => simp [countAt] at positive
  | cons row rows ih =>
    by_cases yes : key row = target ∧ weight row = 1
    · exact ⟨row,by simp,yes.2,yes.1⟩
    · have rest : 0 < countAt rows key weight target := by simpa [countAt,yes] using positive
      obtain ⟨a,member,one,same⟩ := ih rest
      exact ⟨a,by simp [member],one,same⟩

/-- Pure Euclidean arithmetic, before native row sampling. -/
theorem quotient {n bit : Nat} (bound : n ≤ 68719468544) (boolean : bit ≤ 1)
    (balance : (n : F) = (bit : F)) :
    n % mersenne31Modulus = bit ∧ ∃ q ≤ 31, n = bit + mersenne31Modulus*q := by
  have small : bit < mersenne31Modulus := by change bit < 2147483647; omega
  have rem := congrArg ZMod.val balance
  simp only [ZMod.val_natCast,ZMod.val_cast_of_lt small] at rem
  have division := Nat.mod_add_div n mersenne31Modulus
  refine ⟨rem,⟨n / mersenne31Modulus,?_,?_⟩⟩
  · change n / 2147483647 ≤ 31
    omega
  · omega

open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

theorem from_prior {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (capacity : Airbender.NativeMainBatch.Effects batch.main)
    (prior : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs)
    (validity : Airbender.NativeCallerValidity.Effects batch.main.proofs) :
    Airbender.NativeCallerCount.Effects batch workers inputs := by
  have boolean : ∀ w ∈ callerRows batch.main.proofs, w 92 = 0 ∨ w 92 = 1 := by
    intro w member
    simpa [csrRequest,Airbender.ReducedMachine.NativeCSRFieldProofs.request_columns] using (validity w member).boolean
  have counts : ∀ target, occurrences batch.main.proofs target ≤ 68719468544 ∧
      occurrences batch.main.proofs target % mersenne31Modulus = indicator workers target ∧
        ∃ q ≤ 31, occurrences batch.main.proofs target = indicator workers target + mersenne31Modulus*q := by
    intro target
    have bound := (count_bound (callerRows batch.main.proofs) callerKey (fun w => w 92) target).trans capacity.ordinaryBound
    have cast := count_cast (callerRows batch.main.proofs) callerKey (fun w => w 92) target boolean
    have balance : (occurrences batch.main.proofs target : F) = (indicator workers target : F) := by
      rw [occurrences,cast]
      simpa [Airbender.NativeDelegationKeyAccounting.callerWeight,indicator] using prior.callerCoefficients target
    have bit : indicator workers target ≤ 1 := by unfold indicator; split_ifs <;> omega
    exact ⟨bound,quotient bound bit balance⟩
  refine ⟨prior,validity,counts,?_,?_,?_,?_⟩
  · intro target absent
    obtain ⟨q,_,same⟩ := (counts target).2.2
    simp only [indicator,if_neg absent] at same
    change occurrences batch.main.proofs target = 0 ∨ 2147483647 ≤ occurrences batch.main.proofs target
    change occurrences batch.main.proofs target = 0 + 2147483647*q at same
    omega
  · intro target present
    obtain ⟨q,_,same⟩ := (counts target).2.2
    simp only [indicator,if_pos present] at same
    change occurrences batch.main.proofs target = 1 ∨ 2147483648 ≤ occurrences batch.main.proofs target
    change occurrences batch.main.proofs target = 1 + 2147483647*q at same
    omega
  · intro target different
    obtain ⟨q,_,same⟩ := (counts target).2.2
    have nonzero : q ≠ 0 := by
      intro zero
      exact different (by simpa only [zero,Nat.mul_zero,Nat.add_zero] using same)
    have bound := count_bound (callerRows batch.main.proofs) callerKey (fun w => w 92) target
    have slots := Airbender.NativeMainBatchProofs.ordinary_count batch.main
    change (callerRows batch.main.proofs).length = batch.main.proofs.length*Airbender.NativeMainBatch.capacity at slots
    rw [Airbender.NativeMainBatchProofs.geometry.1] at slots
    have count := capacity.count
    change occurrences batch.main.proofs target = indicator workers target + 2147483647*q at same
    change countAt (callerRows batch.main.proofs) callerKey (fun w => w 92) target = _ at same
    change 257 ≤ batch.main.countWord.toNat
    omega
  · intro target present
    obtain ⟨q,_,same⟩ := (counts target).2.2
    simp only [indicator,if_pos present] at same
    have positive : 0 < occurrences batch.main.proofs target := by omega
    exact count_positive _ _ _ _ positive

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
    Airbender.NativeCallerCount.Effects batch workers inputs := by
  have prior := Airbender.NativeCallerValidityProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact from_prior (Airbender.NativeMainBatchProofs.effects batch.main accepted.counted.counter) prior.1 prior.2.2
end Airbender.NativeCallerCountProofs
