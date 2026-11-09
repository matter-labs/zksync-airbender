import Airbender.Review.Trace.Families.ReducedMachine.ControlLastResetTheorems
import Tests.NativeControlLoad

namespace Airbender.Tests.NativeControlLastReset
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure finite tokens/labels, not accepted native rows or physical schedules. -/
private def token (time low high : Nat) : Token := ⟨address,(time,0),Nat.pair low high⟩
private def path : List Token := [token 0 0 0,token 1 0 0,token 2 0 1,token 3 0 1,token 4 3 1,token 5 0 1,token 6 0 1]
private def chosen (index : Fin 6) : Prop := index.val = 1 ∨ index.val = 3

theorem last_change_after_first_origin : ∃ last : Fin 6, last.val = 3 ∧ chosen last ∧
    ∀ index : Fin 6, last.val < index.val → ¬ chosen index := by
  rcases Airbender.NativeControlLastResetProofs.last_position chosen with none | found
  · exact False.elim (none 3 (Or.inr rfl))
  · obtain ⟨last,selected,maximal⟩ := found
    have position : last.val = 3 := by
      rcases selected with first | third
      · have excluded := maximal 3 (by change last.val < 3; omega)
        exact False.elim (excluded (Or.inr rfl))
      · exact third
    exact ⟨last,position,selected,maximal⟩

theorem no_selected_positions : ∀ _ : Fin 0, ¬ True := by intro index; exact Fin.elim0 index

theorem copy_only_no_change : ∀ _ : Fin 6, ¬ (False : Prop) := by intro _ absent; exact absent

theorem original_position_retained : edgeAt path ⟨6,by decide⟩ ⟨3,by decide⟩ = (token 3 0 1,token 4 3 1) := by decide +kernel

theorem first_origin_is_earlier : (limbs (edgeAt path ⟨6,by decide⟩ ⟨1,by decide⟩).1).2 = 0 ∧
    (limbs (edgeAt path ⟨6,by decide⟩ ⟨1,by decide⟩).2).2 = 1 := by decide +kernel

theorem later_change_keeps_high : (limbs (edgeAt path ⟨6,by decide⟩ ⟨3,by decide⟩).1).2 = 1 ∧
    (limbs (edgeAt path ⟨6,by decide⟩ ⟨3,by decide⟩).2).2 = 1 ∧
    (edgeAt path ⟨6,by decide⟩ ⟨3,by decide⟩).1.value ≠ (edgeAt path ⟨6,by decide⟩ ⟨3,by decide⟩).2.value := by decide +kernel

theorem raw_refresh_retained : (token 0 0 0).value = (token 1 0 0).value ∧ (token 0 0 0).time ≠ (token 1 0 0).time := by decide +kernel

theorem equal_value_worker_stays : Updated (token 2 0 1,token 3 0 1) ∧
    (token 2 0 1,token 3 0 1) ∈ path.zip path.tail := by unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh; decide +kernel

theorem worker_clears_incoming_low : Updated (token 4 3 1,token 5 0 1) ∧
    (limbs (token 4 3 1)).1 = 3 := by unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh; decide +kernel

theorem multiple_masks_retained : Updated (token 0 0 24,token 1 0 48) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh; decide +kernel

theorem zero_masks_retained : Updated (token 0 0 0,token 1 0 0) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh; decide +kernel

theorem wrong_worker_high_rejected : ¬ Updated (token 0 0 0,token 1 0 1) := by
  unfold Updated limbs token Airbender.NativeWorkerSchedule.nextHigh; decide +kernel

theorem inactive_CSR_kept : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlLoad.inactive_CSR_kept

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}

theorem every_suffix_edge_actual {nodes : List Token} {target : Fin nodes.length} {start : Nat}
    (suffix : Suffix batch.main.proofs workers nodes target start) (index : Fin target.val) (later : start ≤ index.val) :
    ¬ Relevant batch.main.proofs (edgeAt nodes target index) ∧ WorkerOrCopy batch.main.proofs workers (edgeAt nodes target index) := suffix index later

theorem no_reset_both_zero {nodes : List Token} (history : History batch.main.proofs workers inputs nodes)
    (target : Fin nodes.length) (suffix : Suffix batch.main.proofs workers nodes target 0) : limbs (nodes.get target) = (0,0) :=
  Airbender.NativeControlLastResetProofs.seed_suffix_zero history target suffix

theorem nonzero_target_last_reset {nodes : List Token} {target : Fin nodes.length}
    (result : Outcome before publicSetup batch.main.proofs workers nodes target) (nonzero : (limbs (nodes.get target)).2 ≠ 0) :
    ∃ index : Fin target.val, Relevant batch.main.proofs (edgeAt nodes target index) ∧ PublicWrite before publicSetup batch.main.proofs (edgeAt nodes target index) ∧
      (limbs (edgeAt nodes target index).2).2 ≠ 0 ∧ Suffix batch.main.proofs workers nodes target (index.val+1) :=
  Airbender.NativeControlLastResetProofs.nonzero_reset result nonzero

variable (effect : Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs)
include effect

theorem every_target_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    ∀ target : Fin nodes.length, Outcome before publicSetup batch.main.proofs workers nodes target := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,results,_⟩ := effect.path
  exact ⟨nodes,history,results⟩

theorem every_actual_worker_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin nodes.length, nodes.get target = read w 42 ∧ Outcome before publicSetup batch.main.proofs workers nodes target := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,_,positions⟩ := effect.path
  exact ⟨nodes,history,positions⟩

theorem all_ordinary_CSR_edges_retained : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    Edges csrDecoderFields batch.main.proofs nodes ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs nodes ∧
    Edges bitwiseDecoderFields batch.main.proofs nodes ∧ Edges comparisonDecoderFields batch.main.proofs nodes ∧
    Edges shiftDecoderFields batch.main.proofs nodes ∧ Edges jumpDecoderFields batch.main.proofs nodes ∧
    Edges wordMemoryDecoderFields batch.main.proofs nodes ∧
    ∀ target : Fin nodes.length, Outcome before publicSetup batch.main.proofs workers nodes target := by
  obtain ⟨nodes,history,_,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,_⟩ := effect.path
  exact ⟨nodes,history,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results⟩

theorem prior_values_retained : Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs := effect.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior
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
    Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlLastResetProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlLastReset
