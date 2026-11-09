import Airbender.Review.Trace.Families.ReducedMachine.ControlFoldTheorems
import Tests.NativeControlLastReset

namespace Airbender.Tests.NativeControlFold
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.NativeControlFold
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure small position labels and values; not actual accepted native rows. -/
private def flags (index : Fin 3) : Bool := decide (index.val = 0 ∨ index.val = 2)
private def values (index : Fin 4) : Nat × Nat :=
  match index.val with
  | 0 => (9,24)
  | 1 => (0,48)
  | 2 => (0,48)
  | _ => (0,96)

theorem two_selected_positions : countFlags flags = 2 := by decide +kernel
theorem all_equal_value_updates_counted : countFlags (fun _ : Fin 3 => true) = 3 ∧ iterate advance 3 (0,1) = (0,1) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem empty_positions : countFlags (fun index : Fin 0 => Fin.elim0 index) = 0 := rfl
theorem no_worker_keeps_low : iterate advance 0 (9,24) = (9,24) := rfl
theorem first_worker_clears_low : iterate advance 1 (9,24) = (0,48) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem multiple_masks_shift_twice : iterate advance 2 (9,24) = (0,96) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem zero_masks_still_update : iterate advance 2 (9,0) = (0,0) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem incoming_mode_bits_remain : iterate advance 3 (9,31) = (0,199) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem last_mask_exits : iterate advance 1 (9,4096) = (0,0) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem ten_updates_exhaust_two_masks : iterate advance 10 (9,24) = (0,0) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem wrong_count_result_rejected : iterate advance 1 (9,24) ≠ iterate advance 2 (9,24) := by
  unfold advance Airbender.NativeWorkerSchedule.nextHigh; decide +kernel
theorem derived_finite_fold : values 3 = iterate advance (countFlags flags) (values 0) := by
  apply Airbender.NativeControlFoldProofs.selected_fold advance 3 values flags
  unfold values flags advance Airbender.NativeWorkerSchedule.nextHigh
  decide +kernel
theorem bounded_original_positions (n : Nat) (selected : Fin n → Bool) : countFlags selected ≤ n :=
  Airbender.NativeControlFoldProofs.count_bound n selected
theorem exact_zero_positions (n : Nat) (selected : Fin n → Bool) : countFlags selected = 0 ↔ ∀ index, selected index = false :=
  Airbender.NativeControlFoldProofs.count_zero_iff n selected
theorem inactive_CSR_kept : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlLastReset.inactive_CSR_kept

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}

theorem actual_worker_position_selected (nodes : List Token) (target : Fin nodes.length) (start : Fin (target.val+1))
    (index : Fin (target.val-start.val)) : workerFlags workers nodes target start index = true ↔
      WorkerEdge workers (edgeAt nodes target ⟨start.val + index.val,by have := index.isLt; omega⟩) :=
  Airbender.NativeControlFoldProofs.flags_match workers nodes target start index

theorem actual_count_bound (nodes : List Token) (target : Fin nodes.length) (start : Fin (target.val+1)) :
    workerCount workers nodes target start ≤ target.val-start.val :=
  Airbender.NativeControlFoldProofs.worker_count_bound workers nodes target start

theorem zero_count_exactly_no_workers (nodes : List Token) (target : Fin nodes.length) (start : Fin (target.val+1)) :
    workerCount workers nodes target start = 0 ↔ ∀ index : Fin (target.val-start.val),
      ¬ WorkerEdge workers (edgeAt nodes target ⟨start.val + index.val,by have := index.isLt; omega⟩) :=
  Airbender.NativeControlFoldProofs.worker_count_zero_iff workers nodes target start

theorem actual_suffix_fold {nodes : List Token} (target : Fin nodes.length) (start : Fin (target.val+1))
    (rows : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerTransition.RowEffects w)
    (suffix : Suffix batch.main.proofs workers nodes target start.val) : Fold workers nodes target start :=
  Airbender.NativeControlFoldProofs.suffix_fold target start rows suffix

theorem no_workers_copy_both {nodes : List Token} {target : Fin nodes.length} {start : Fin (target.val+1)}
    (result : Fold workers nodes target start) (zero : workerCount workers nodes target start = 0) :
    limbs (nodes.get target) = limbs (nodes.get ⟨start.val,by have := start.isLt; have := target.isLt; omega⟩) :=
  Airbender.NativeControlFoldProofs.no_worker_copy result zero

variable (effect : Airbender.NativeControlFold.Effects before publicSetup batch workers inputs)
include effect

theorem every_target_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    ∀ target : Fin nodes.length, Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,results,_⟩ := effect.path
  exact ⟨nodes,history,results⟩

theorem every_actual_worker_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin nodes.length, nodes.get target = read w 42 ∧
        Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,_,positions⟩ := effect.path
  exact ⟨nodes,history,positions⟩

theorem all_ordinary_CSR_edges_retained : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    Edges csrDecoderFields batch.main.proofs nodes ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs nodes ∧
    Edges bitwiseDecoderFields batch.main.proofs nodes ∧ Edges comparisonDecoderFields batch.main.proofs nodes ∧
    Edges shiftDecoderFields batch.main.proofs nodes ∧ Edges jumpDecoderFields batch.main.proofs nodes ∧
    Edges wordMemoryDecoderFields batch.main.proofs nodes ∧
    ∀ target : Fin nodes.length, Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target := by
  obtain ⟨nodes,history,_,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,_⟩ := effect.path
  exact ⟨nodes,history,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results⟩

theorem prior_last_reset_retained : Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs := effect.prior
theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs :=
  Airbender.Tests.NativeControlLastReset.old_joint_retained effect.prior
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
    Airbender.NativeControlFold.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlFoldProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlFold
