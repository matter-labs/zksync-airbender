import Airbender.Review.Trace.Families.ReducedMachine.ControlOriginTheorems
import Tests.NativeControlHistory

namespace Airbender.Tests.NativeControlOrigin
open Airbender.NativeControlHistory Airbender.NativeControlOrigin Airbender.NativeWorkerSnapshot
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Small generic ordered data only, not native-global accepted witnesses. -/
private def path : List (Nat × Nat) := [(0,0),(1,0),(2,8),(3,16),(4,0)]

theorem first_nonzero_origin : ∃ a b, (a,b) ∈ path.zip path.tail ∧ a.2 = 0 ∧ b.2 ≠ 0 ∧ b.1 ≤ 3 := by
  exact Airbender.NativeControlOriginProofs.zero_origin Prod.snd Prod.fst (0,0)
    [(1,0),(2,8),(3,16),(4,0)] rfl (by decide +kernel) (target := (3,16)) (by decide +kernel) (by decide +kernel)

theorem exact_first_edge : (((1,0),(2,8)) : (Nat × Nat) × (Nat × Nat)) ∈ path.zip path.tail := by decide +kernel

theorem refresh_is_not_origin : ¬ (((0,0),(1,0)) : (Nat × Nat) × (Nat × Nat)).2.2 ≠ 0 := by decide +kernel

theorem later_worker_is_not_first_origin : ¬ (((2,8),(3,16)) : (Nat × Nat) × (Nat × Nat)).1.2 = 0 := by decide +kernel

theorem final_zero_retained : (4,0) ∈ path := by decide +kernel

theorem duplicate_rank_rejected : ¬ (([(0,0),(1,8),(1,16)] : List (Nat × Nat)).map Prod.fst).Pairwise (· < ·) := by decide +kernel

theorem multiple_mask_retained : Airbender.NativeWorkerSchedule.nextHigh 24 = 48 := by decide +kernel

theorem last_mask_drops : Airbender.NativeWorkerSchedule.nextHigh 4096 = 0 := by decide +kernel

theorem zero_worker_cannot_seed_nonzero {edge : Token × Token} (update : Updated edge) (zero : (limbs edge.1).2 = 0) :
    (limbs edge.2).2 = 0 := Airbender.NativeControlOriginProofs.worker_zero edge update zero

theorem actual_MAIN_change_is_third {row : Airbender.NativeMixedMemoryOrder.MainRow} {edge : Token × Token}
    (member : edge ∈ row.memorySteps) (changed : edge.1.value ≠ edge.2.value) :
    edge = (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) :=
  Airbender.NativeControlOriginProofs.third_of_change member changed

theorem actual_readonly_ports_copy (w : Nat → F) (slot : Fin 3) (small : slot.val < 2) :
    Airbender.NativeMainDependencies.writeWord w slot = Airbender.NativeMainDependencies.readWord w slot :=
  Airbender.NativeMainDependencyProofs.readonly_values w slot small

theorem inactive_caller_retained : Airbender.NativeCallerValidity.RowEffects
    (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) :=
  Airbender.Tests.NativeControlHistory.inactive_request_retained

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
  (effect : Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs)
include effect

theorem complete_history_with_origins : ∃ p, History batch.main.proofs workers inputs p ∧
    ∀ token ∈ p, (limbs token).2 ≠ 0 → Origin before publicSetup batch.main.proofs token := effect.origins

theorem every_nonzero_worker_origin {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) (nonzero : (w 135).val ≠ 0) :
    Origin before publicSetup batch.main.proofs (read w 42) := effect.workers w member active nonzero

theorem old_history_retained : Airbender.NativeControlHistory.Effects batch workers inputs := effect.prior

theorem old_position_matching_retained : Airbender.NativeCallerPosition.Effects batch workers inputs := effect.prior.prior

theorem old_counts_retained : Airbender.NativeCallerCount.Effects batch workers inputs := effect.prior.prior.prior

theorem old_joint_execution_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior
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
    Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlOriginProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlOrigin
