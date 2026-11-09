import Airbender.Review.Trace.Families.ReducedMachine.CallerPositionTheorems
import Tests.NativeCallerCount

namespace Airbender.Tests.NativeCallerPosition
open Airbender.NativeDelegationSupport Airbender.NativeCallerPosition
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Small pure lists only: original positions and both directions matter. -/
theorem reversed_order_matches : IndexMatching [3,7] [7,3] id id (fun _ : Nat => (1 : F)) (fun _ : Nat => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem duplicate_callers_rejected : ¬ IndexMatching [3,3] [3] id id (fun _ : Nat => (1 : F)) (fun _ : Nat => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem duplicate_workers_rejected : ¬ IndexMatching [3] [3,3] id id (fun _ : Nat => (1 : F)) (fun _ : Nat => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem missing_worker_rejected : ¬ IndexMatching [3] ([] : List Nat) id id (fun _ : Nat => (1 : F)) (fun _ : Nat => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem missing_caller_rejected : ¬ IndexMatching ([] : List Nat) [3] id id (fun _ : Nat => (1 : F)) (fun _ : Nat => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem wrong_key_rejected : ¬ IndexMatching [3] [7] id id (fun _ : Nat => (1 : F)) (fun _ : Nat => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem retained_zero_positions : IndexMatching [0,3,0] [3,0] id id (fun n : Nat => if n = 0 then (0 : F) else 1)
    (fun n : Nat => if n = 0 then (0 : F) else 1) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem empty_positions : IndexMatching ([] : List Nat) ([] : List Nat) id id (fun _ => (1 : F)) (fun _ => (1 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem zero_weight_only : IndexMatching [3,3] [7] id id (fun _ : Nat => (0 : F)) (fun _ : Nat => (0 : F)) := by
  unfold IndexMatching ExistsUnique
  decide +kernel

theorem inactive_request_retained : Airbender.NativeCallerValidity.RowEffects
    (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) :=
  Airbender.Tests.NativeCallerValidity.inactive_validity

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} (effect : Effects batch workers inputs)
include effect

theorem exact_dichotomy : Matching batch workers ∨ 257 ≤ batch.countWord.toNat := effect.matching_or_large

theorem small_batch_matching (small : batch.countWord.toNat ≤ 256) : Matching batch workers := by
  rcases effect.matching_or_large with matched | large
  · exact matched
  · omega

theorem caller_unique_partner (small : batch.countWord.toNat ≤ 256)
    (i : Fin (callerRows batch.main.proofs).length) (request : (callerRows batch.main.proofs)[i.val] 92 = 1) :
    ∃! j : Fin (Airbender.NativeTokenLedger.workerRows workers).length,
      (Airbender.NativeTokenLedger.workerRows workers)[j.val] constraintsABI.multiplicity = 1 ∧
        callerKey (callerRows batch.main.proofs)[i.val] = workerKey (Airbender.NativeTokenLedger.workerRows workers)[j.val] :=
  (small_batch_matching effect small).1 i request

theorem worker_unique_partner (small : batch.countWord.toNat ≤ 256)
    (j : Fin (Airbender.NativeTokenLedger.workerRows workers).length)
    (active : (Airbender.NativeTokenLedger.workerRows workers)[j.val] constraintsABI.multiplicity = 1) :
    ∃! i : Fin (callerRows batch.main.proofs).length,
      (callerRows batch.main.proofs)[i.val] 92 = 1 ∧
        callerKey (callerRows batch.main.proofs)[i.val] = workerKey (Airbender.NativeTokenLedger.workerRows workers)[j.val] :=
  (small_batch_matching effect small).2 j active

theorem all_count_results_retained : Airbender.NativeCallerCount.Effects batch workers inputs := effect.prior

theorem joint_execution_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior
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
    Airbender.NativeCallerPosition.Effects batch workers inputs :=
  Airbender.NativeCallerPositionProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeCallerPosition
