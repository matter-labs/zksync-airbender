import Airbender.Review.Trace.Families.ReducedMachine.CallerCountTheorems
import Tests.NativeCallerValidity

namespace Airbender.Tests.NativeCallerCount
open Airbender.NativeDelegationSupport Airbender.NativeCallerCount
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Small pure lists retain duplicate positions and zero weights. -/
theorem duplicate_positions : countAt [1,1,0,2] id (fun _ : Nat => (1 : F)) 1 = 2 := by decide +kernel

theorem zero_weights : countAt [0,1,0] (fun _ : Nat => 0) (fun n => (n : F)) 0 = 1 := by decide +kernel

theorem absent_key : countAt [1,1,2] id (fun _ : Nat => (1 : F)) 3 = 0 := by decide +kernel

theorem empty_count : countAt ([] : List Nat) id (fun _ => (1 : F)) 0 = 0 := rfl

theorem occurrence_bound : countAt [1,1,0,2] id (fun _ : Nat => (1 : F)) 1 ≤ 4 :=
  Airbender.NativeCallerCountProofs.count_bound _ _ _ _

/-- Scalar arithmetic only, not characteristic-sized native row witnesses. -/
theorem field_characteristic_retained : (mersenne31Modulus : F) = 0 ∧ 0 < mersenne31Modulus := by decide +kernel

theorem main_capacity_below_32_characteristics : 68719468544 < 32*mersenne31Modulus := by decide +kernel

theorem quotient31_arithmetic : ∃ q ≤ 31, 66571993058 = 1 + mersenne31Modulus*q := by
  exact ⟨31,by decide +kernel,by decide +kernel⟩

theorem no_wrap_not_inferred : (mersenne31Modulus : F) = (0 : F) ∧ mersenne31Modulus ≠ (0 : Nat) := by decide +kernel

theorem inactive_valid_request_retained : Airbender.NativeCallerValidity.RowEffects
    (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) :=
  Airbender.Tests.NativeCallerValidity.inactive_validity

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} (effect : Airbender.NativeCallerCount.Effects batch workers inputs)
include effect

theorem natural_bound (target : Key) : occurrences batch.main.proofs target ≤ 68719468544 := (effect.perKey target).1

theorem exact_remainder (target : Key) : occurrences batch.main.proofs target % mersenne31Modulus = indicator workers target :=
  (effect.perKey target).2.1

theorem bounded_quotient (target : Key) : ∃ q ≤ 31, occurrences batch.main.proofs target = indicator workers target + mersenne31Modulus*q :=
  (effect.perKey target).2.2

theorem unfulfilled_requires_characteristic (target : Key) (absent : target ∉ Airbender.NativeDelegationKeyAccounting.keys workers)
    (present : occurrences batch.main.proofs target ≠ 0) : mersenne31Modulus ≤ occurrences batch.main.proofs target :=
  (effect.missing target absent).resolve_left present

theorem repeated_fulfilled_requires_characteristic (target : Key) (present : target ∈ Airbender.NativeDelegationKeyAccounting.keys workers)
    (repeated : occurrences batch.main.proofs target ≠ 1) : mersenne31Modulus+1 ≤ occurrences batch.main.proofs target :=
  (effect.repeated target present).resolve_left repeated

theorem worker_has_actual_caller (target : Key) (present : target ∈ Airbender.NativeDelegationKeyAccounting.keys workers) :
    ∃ caller ∈ callerRows batch.main.proofs, caller 92 = 1 ∧ callerKey caller = target := effect.workerCaller target present

theorem wrap_requires257_proofs (target : Key) (different : occurrences batch.main.proofs target ≠ indicator workers target) :
    257 ≤ batch.countWord.toNat := effect.wrapRequiresProofs target different

theorem up_to256_exact (small : batch.countWord.toNat ≤ 256) (target : Key) :
    occurrences batch.main.proofs target = indicator workers target := by
  by_contra different
  have large := effect.wrapRequiresProofs target different
  omega

theorem individual_validity_retained : Airbender.NativeCallerValidity.Effects batch.main.proofs := effect.validity

theorem joint_execution_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior
end

theorem full_counted_source {Setup R : Type} [Field R]
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
    Airbender.NativeCallerCount.Effects batch workers inputs :=
  Airbender.NativeCallerCountProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeCallerCount
