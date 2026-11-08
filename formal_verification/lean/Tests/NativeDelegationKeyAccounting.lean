import Airbender.Review.Trace.Families.ReducedMachine.DelegationKeyAccountingTheorems
import Tests.NativeJointReplay

namespace Airbender.Tests.NativeDelegationKeyAccounting
open Airbender.NativeDelegationSupport Airbender.NativeDelegationKeyAccounting
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Small generic weighted lists only, not accepted native/physical witnesses. -/
private def cancelling : List (Nat × F) := [(7,1),(7,-1)]
private def aggregateOne : List (Nat × F) := [(7,2),(7,-1)]
private def workers : List (Nat × F) := [(7,1),(9,0),(11,1)]

theorem cancelling_rows_nonzero : ∀ row ∈ cancelling, row.2 ≠ 0 := by decide +kernel

theorem cancelling_aggregate_zero : weightAt cancelling Prod.fst Prod.snd 7 = 0 := by decide +kernel

theorem nonboolean_rows_aggregate_one : weightAt aggregateOne Prod.fst Prod.snd 7 = 1 := by decide +kernel

theorem worker_unique_keys : ((workers.filter fun row => row.2 = 1).map Prod.fst).Nodup := by decide +kernel

theorem exact_small_indicator (target : Nat) : weightAt workers Prod.fst Prod.snd target =
    if target ∈ (workers.filter fun row => row.2 = 1).map Prod.fst then 1 else 0 := by
  apply Airbender.NativeDelegationKeyAccountingProofs.unique_weight
  · decide +kernel
  · exact worker_unique_keys

theorem absent_small_key : weightAt workers Prod.fst Prod.snd 5 = 0 := by decide +kernel

theorem duplicate_active_key_rejected : ¬
    ((([(7,1),(7,1)] : List (Nat × F)).filter fun row => row.2 = 1).map Prod.fst).Nodup := by decide +kernel

theorem selection_retains_duplicates :
    (([0,1,0] : List Nat).filter fun n => decide (n = 0)).map id = [0,0] := rfl

theorem selected_edges_sublist :
    (([0,1,0] : List Nat).filter fun n => decide (n = 0)).Sublist
      (([0,1,0] : List Nat).flatMap fun n => if n = 0 then [n,n+2] else []) := by
  decide +kernel

theorem actual_x12_descriptor : (keyDescriptor (42 : Fin 43)).location = .register 12 :=
  Airbender.NativeDelegationKeyAccountingProofs.control_descriptor

theorem actual_x12_address (w : Nat → F) :
    (Airbender.NativeWorkerSnapshot.write w 42).address = Nat.pair 0 (Nat.pair 12 0) :=
  Airbender.NativeDelegationKeyAccountingProofs.control_address w

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {selected : WorkerBatch Setup R} {inputs : PublicBoundary}
  (effect : Airbender.NativeDelegationKeyAccounting.Effects batch selected inputs)
include effect

theorem active_raw_clock_pairs_unique :
    ((activeRows selected).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup := effect.clocksUnique

theorem full_raw_keys_unique : (keys selected).Nodup := effect.keysUnique

theorem all_worker_coefficients (target : Key) :
    workerWeight selected target = if target ∈ keys selected then 1 else 0 := effect.workerCoefficients target

theorem all_caller_coefficients (target : Key) :
    callerWeight batch.main.proofs target = if target ∈ keys selected then 1 else 0 := effect.callerCoefficients target

theorem exact_aggregate_converse (target : Key) :
    callerWeight batch.main.proofs target ≠ 0 ↔ target ∈ keys selected := effect.converse target

theorem full_joint_execution_retained : Airbender.NativeJointReplay.Execution batch.main.proofs selected inputs :=
  effect.prior.joint
end

theorem main_partial_dependencies_retained : ¬ (Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.read (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 2) <
    Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 0)) :=
  Airbender.Tests.NativeWorkerGroup.main_partial_dependencies_retained

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerGroup.inactive_requests_retained

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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs :=
  Airbender.NativeDelegationKeyAccountingProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeDelegationKeyAccounting
