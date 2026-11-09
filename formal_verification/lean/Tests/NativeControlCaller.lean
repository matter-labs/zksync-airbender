import Airbender.Review.Trace.Families.ReducedMachine.ControlCallerTheorems
import Tests.NativeControlSource
import Tests.NativeCallerPosition

namespace Airbender.Tests.NativeControlCaller
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.NativeControlFold Airbender.NativeControlSource Airbender.NativeControlCaller
open Airbender.NativeDelegationSupport (callerRows callerKey workerKey)
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure finite position labels and raw-key data; not native accepted witnesses. -/
private def key : CSRArgumentKey F := ⟨1991,4,7,0⟩

theorem composed_original_indices : ∃! caller : Fin 4, ∃ source : Fin 3, source.val = 2 ∧ caller.val + source.val = 2 := by
  apply Airbender.NativeControlCallerProofs.unique_compose (fun source : Fin 3 => source.val = 2)
    (fun source (caller : Fin 4) => caller.val + source.val = 2)
  · unfold ExistsUnique; decide +kernel
  · unfold ExistsUnique; decide +kernel

theorem duplicate_caller_positions_rejected : ¬ (∃! caller : Fin 3, ∃ source : Fin 2,
    source.val = 0 ∧ (caller.val = 0 ∨ caller.val = 2)) := by
  unfold ExistsUnique
  decide +kernel

theorem empty_source_has_no_partner : ¬ (∃! _ : Fin 0, True) := by
  unfold ExistsUnique
  decide +kernel

theorem wrong_kind_rejected : (⟨1984,4,7,0⟩ : CSRArgumentKey F) ≠ key := by decide +kernel
theorem wrong_ABI_rejected : (⟨1991,5,7,0⟩ : CSRArgumentKey F) ≠ key := by decide +kernel
theorem wrong_low_rejected : (⟨1991,4,8,0⟩ : CSRArgumentKey F) ≠ key := by decide +kernel
theorem wrong_high_rejected : (⟨1991,4,7,1⟩ : CSRArgumentKey F) ≠ key := by decide +kernel

theorem raw_caller_clock_wrap_kept : (2147483646 : F) + 3 = 2 := by decide +kernel

theorem inactive_request_positive : NativeCSRPositiveWitness.assignment false 4 = 0 ∧
    NativeCSRPositiveWitness.assignment false 92 = 1 := by decide +kernel

theorem old_LOCAL_inactive_validity : Airbender.NativeCallerValidity.RowEffects (NativeCSRPositiveWitness.assignment false) :=
  Airbender.Tests.NativeCallerPosition.inactive_request_retained

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
  {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}

theorem exact_source_kept {edge : Token × Token} {caller : Fin (callerRows batch.main.proofs).length}
    (matched : CallerAt batch.main.proofs workers edge caller) : WorkerEdge workers edge :=
  Airbender.NativeControlCallerProofs.caller_member matched

theorem all_four_raw_fields {edge : Token × Token} {caller : Fin (callerRows batch.main.proofs).length}
    (matched : CallerAt batch.main.proofs workers edge caller) :
    ∃ source : Fin (Airbender.NativeTokenLedger.workerRows workers).length, SourceAt workers edge source ∧
      (callerRows batch.main.proofs)[caller.val] 92 = 1 ∧ (callerRows batch.main.proofs)[caller.val] 94 = 1991 ∧
      (callerRows batch.main.proofs)[caller.val] 93 = (Airbender.NativeTokenLedger.workerRows workers)[source.val] 1 ∧
      ((callerRows batch.main.proofs)[caller.val] 2 + 3,(callerRows batch.main.proofs)[caller.val] 3) = edge.2.time :=
  Airbender.NativeControlCallerProofs.caller_fields matched

theorem segment_counts_conditional (partners : Airbender.NativeCallerPosition.Matching batch workers)
    (nodes : List Token) (target : Fin nodes.length) (start : Fin (target.val+1)) :
    sourceCount workers nodes target start = callerCount batch.main.proofs workers nodes target start :=
  Airbender.NativeControlCallerProofs.segment_count partners nodes target start

theorem caller_count_original_bound (nodes : List Token) (target : Fin nodes.length) (start : Fin (target.val+1)) :
    callerCount batch.main.proofs workers nodes target start ≤ (callerRows batch.main.proofs).length :=
  Airbender.NativeControlCallerProofs.caller_count_bound batch.main.proofs workers nodes target start

variable (effect : Airbender.NativeControlCaller.Effects before publicSetup batch workers inputs)
include effect

theorem unconditional_original_caller : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    ∀ index : Fin (nodes.length-1), WorkerEdge workers (pathEdge nodes index) →
      ∃ caller, CallerAt batch.main.proofs workers (pathEdge nodes index) caller := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,_,_,_,_,origins,_⟩ := effect.path
  exact ⟨nodes,history,origins⟩

theorem same_path_dichotomy : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    (Accounting batch.main.proofs workers nodes ∨ 257 ≤ batch.countWord.toNat) := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,_,_,_,_,_,scope⟩ := effect.path
  exact ⟨nodes,history,scope⟩

theorem small_batch_scope (small : batch.countWord.toNat ≤ 256) :
    ∃ nodes, History batch.main.proofs workers inputs nodes ∧ Accounting batch.main.proofs workers nodes := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,_,_,_,_,_,scope⟩ := effect.path
  rcases scope with accounting | large
  · exact ⟨nodes,history,accounting⟩
  · omega

theorem all_targets_and_workers_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    (∀ target : Fin nodes.length, Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target) ∧
    (∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ target : Fin nodes.length, nodes.get target = read w 42 ∧ Airbender.NativeControlFold.Outcome before publicSetup batch.main.proofs workers nodes target) ∧
    (Accounting batch.main.proofs workers nodes ∨ 257 ≤ batch.countWord.toNat) := by
  obtain ⟨nodes,history,_,_,_,_,_,_,_,_,results,positions,_,_,_,scope⟩ := effect.path
  exact ⟨nodes,history,results,positions,scope⟩

theorem all_ordinary_CSR_edges_same_path : ∃ nodes, History batch.main.proofs workers inputs nodes ∧
    Edges csrDecoderFields batch.main.proofs nodes ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs nodes ∧
    Edges bitwiseDecoderFields batch.main.proofs nodes ∧ Edges comparisonDecoderFields batch.main.proofs nodes ∧
    Edges shiftDecoderFields batch.main.proofs nodes ∧ Edges jumpDecoderFields batch.main.proofs nodes ∧
    Edges wordMemoryDecoderFields batch.main.proofs nodes ∧
    (Accounting batch.main.proofs workers nodes ∨ 257 ≤ batch.countWord.toNat) := by
  obtain ⟨nodes,history,_,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,_,_,_,_,_,scope⟩ := effect.path
  exact ⟨nodes,history,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,scope⟩

theorem old_source_indices_retained : Airbender.NativeControlSource.Effects before publicSetup batch workers inputs := effect.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs :=
  Airbender.Tests.NativeControlSource.old_joint_retained effect.prior
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
    Airbender.NativeControlCaller.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlCallerProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlCaller
