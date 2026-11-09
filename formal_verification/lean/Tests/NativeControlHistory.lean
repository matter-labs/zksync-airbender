import Airbender.Review.Trace.Families.ReducedMachine.ControlHistoryTheorems
import Tests.NativeCallerPosition

namespace Airbender.Tests.NativeControlHistory
open Airbender.NativeControlHistory Airbender.NativeWorkerSnapshot
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Small raw-token/pure update controls, not globally accepted native witnesses. -/
private def token (low high : Nat) : Token := ⟨address,(0,0),Nat.pair low high⟩

theorem zero_seed : limbs initial = (0,0) := Airbender.NativeControlHistoryProofs.initial_zero

theorem zero_seed_time : initial.time = (0,0) := rfl

theorem seed_address : initial.address = address := Airbender.NativeControlHistoryProofs.initial_address

theorem zero_mask_update : Updated (token 0 0,token 0 0) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem first_round_update : Updated (token 0 8,token 0 16) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem multiple_round_update : Updated (token 0 24,token 0 48) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem last_round_update : Updated (token 0 4096,token 0 0) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem incoming_low_retained : Updated (token 65535 24,token 0 48) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem wrong_high_rejected : ¬ Updated (token 0 8,token 0 32) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem uncleared_low_rejected : ¬ Updated (token 0 8,token 1 16) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel

theorem readonly_gpr11_is_not_control : (memoryAccess 25).writeValue = none ∧
    (keyDescriptor 25).location = .register 11 := by decide +kernel

theorem actual_input_limbs (w : Nat → F) : limbs (read w 42) = ((w 134).val,(w 135).val) :=
  Airbender.NativeControlHistoryProofs.read_limbs w

theorem actual_output_limbs (w : Nat → F) : limbs (write w 42) = ((w 136).val,(w 137).val) :=
  Airbender.NativeControlHistoryProofs.write_limbs w

theorem inactive_request_retained : Airbender.NativeCallerValidity.RowEffects
    (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) :=
  Airbender.Tests.NativeCallerPosition.inactive_request_retained

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} (effect : Airbender.NativeControlHistory.Effects batch workers inputs)
include effect

theorem complete_initial_to_public : ∃ path, History batch.main.proofs workers inputs path := effect.history

theorem full_source_retained : Airbender.NativeCallerPosition.Effects batch workers inputs := effect.prior

theorem joint_execution_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior

omit effect in
theorem control_edges_classified {path : List Token} (history : History batch.main.proofs workers inputs path)
    {edge : Token × Token} (member : edge ∈ path.zip path.tail) : MainEdge batch.main.proofs edge ∨
    ∃ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 ∧
      edge = (read w 42,write w 42) ∧ Updated edge := history.classified edge member

omit effect in
theorem every_worker_on_same_path {path : List Token} (history : History batch.main.proofs workers inputs path)
    {w : Nat → F} (wm : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    (read w 42,write w 42) ∈ path.zip path.tail := history.workers w wm active
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
    Airbender.NativeControlHistory.Effects batch workers inputs :=
  Airbender.NativeControlHistoryProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlHistory
