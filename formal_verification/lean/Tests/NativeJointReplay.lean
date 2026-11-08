import Airbender.Review.Trace.Families.ReducedMachine.JointReplayTheorems
import Tests.NativeWorkerGroup

namespace Airbender.Tests.NativeJointReplay
open Airbender.NativeJointReplay Airbender.NativeWorkerSnapshot Airbender.NativeMixedReplay
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Small generic tokens and block labels, not native/global/physical witnesses. -/
private abbrev Cell := Nat × Nat
private def seeds : List Cell := [(0,0),(1,0),(2,0),(3,0),(9,11)]
private def terminal : List Cell := [(0,3),(1,4),(2,3),(3,3),(9,11)]
private def blocks (group : Fin 4) : List (Cell × Cell) :=
  match group.val with
  | 0 => [((0,0),(0,1))]
  | 1 => [((0,1),(0,3)),((1,0),(1,3))]
  | 2 => [((2,0),(2,3)),((3,0),(3,3))]
  | _ => [((1,3),(1,4))]
private def clock (group : Fin 4) : Nat :=
  if group = 0 then 1 else if group = 3 then 4 else 3
private def source : List (Fin 4) := [3,2,1,0]

theorem full_balance : (seeds ++ (source.flatMap blocks).map Prod.snd).Perm
    (terminal ++ (source.flatMap blocks).map Prod.fst) := by decide +kernel

theorem common_write : ∀ group : Fin 4, ∀ edge ∈ blocks group, edge.2.2 = clock group := by
  decide +kernel

theorem strict_old_reads : ∀ group : Fin 4, ∀ edge ∈ blocks group, edge.1.2 < clock group := by
  decide +kernel

theorem complete_joint : ∃ ordered, ordered.Perm source ∧ ordered.Pairwise (fun a b => clock a ≤ clock b) ∧
    BatchReplay Prod.fst blocks seeds ordered terminal := by
  apply Airbender.NativeJointReplayProofs.batch_exists Prod.fst Prod.snd blocks clock source seeds terminal
  · decide +kernel
  · exact full_balance
  · decide +kernel
  · exact fun group _ => common_write group
  · exact fun group _ => strict_old_reads group

theorem both_workers_in_same_execution : ∃ ordered,
    ordered.Perm source ∧ BatchReplay Prod.fst blocks seeds ordered terminal ∧
    (∀ group ∈ ([1,2] : List (Fin 4)), ∃ before after prior rest,
      ordered = prior ++ group :: rest ∧ BatchReplay Prod.fst blocks seeds prior before ∧
      (∀ edge ∈ blocks group, edge.1 ∈ before) ∧ Replay Prod.fst before (blocks group) after ∧
      BatchReplay Prod.fst blocks after rest terminal) := by
  obtain ⟨ordered,same,_,run⟩ := complete_joint
  refine ⟨ordered,same,run,?_⟩
  intro group member
  apply Airbender.NativeJointReplayProofs.locate Prod.fst blocks run
  apply same.mem_iff.mpr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

theorem tied_blocks : clock 1 = clock 2 := rfl

theorem dependent_worker_not_initially_ready : ¬ (∀ edge ∈ blocks 1, edge.1 ∈ seeds) := by
  decide +kernel

theorem wrong_terminal_rejected : ¬ (seeds ++ (source.flatMap blocks).map Prod.snd).Perm
    ([(0,3),(1,3),(2,3),(3,3),(9,11)] ++ (source.flatMap blocks).map Prod.fst) := by decide +kernel

theorem duplicated_source_changes_balance : ¬ (seeds ++ ((1 :: source).flatMap blocks).map Prod.snd).Perm
    (terminal ++ ((1 :: source).flatMap blocks).map Prod.fst) := by decide +kernel

theorem actual_group_flatten {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R) :
    (groups proofs workers).flatMap edges = Airbender.NativeMemoryRoots.steps proofs workers :=
  Airbender.NativeJointReplayProofs.source_flatten proofs workers

theorem main_is_singleton (edge : Token × Token) : edges (.main edge) = [edge] := rfl

theorem worker_is_all43 (w : Nat → F) : (edges (.worker w)).length = 43 := by
  simp [edges,Airbender.NativeWorkerGroup.ports,Airbender.NativeMemoryRoots.workerSteps]

theorem actual_common_both_times (w : Nat → F) (slot : Fin 43) :
    (write w slot).time = (write w 0).time := by
  rw [Airbender.NativeActiveWorkerClockProofs.write_clock,Airbender.NativeActiveWorkerClockProofs.write_clock]

theorem current_snapshot_reference (w : Nat → F) {before after : List Token}
    (effect : WorkerEffect w before after) (old fresh : Fin 43 → Token)
    (oldPresent : ∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address)
    (newPresent : ∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) :
    Airbender.NativeWorkerGroup.sampledOutput fresh = Airbender.NativeWorkerTransition.transition (sampledInput old) :=
  effect.reference old fresh oldPresent newPresent

theorem all_state_and_extended_outputs (w : Nat → F) {before after : List Token}
    (effect : WorkerEffect w before after) (old fresh : Fin 43 → Token)
    (oldPresent : ∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address)
    (newPresent : ∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) :
    (∀ word, (Airbender.NativeWorkerGroup.sampledOutput fresh).state word =
      (Airbender.NativeWorkerTransition.transition (sampledInput old)).state word) ∧
    (∀ word, (Airbender.NativeWorkerGroup.sampledOutput fresh).extended word =
      (Airbender.NativeWorkerTransition.transition (sampledInput old)).extended word) := by
  rw [effect.reference old fresh oldPresent newPresent]
  exact ⟨fun _ => rfl,fun _ => rfl⟩

theorem exact_post_and_frame (w : Nat → F) {before after : List Token} (effect : WorkerEffect w before after) :
    (∀ slot, write w slot ∈ after) ∧
    (∀ slot token, token ∈ after → token.address = (write w slot).address → token = write w slot) ∧
    (∀ token, (∀ slot, token.address ≠ (write w slot).address) → (token ∈ after ↔ token ∈ before)) :=
  ⟨effect.writes,effect.exact,effect.frame⟩

theorem readonly_refresh_retained (w : Nat → F) {before after : List Token} (effect : WorkerEffect w before after) :
    ∀ slot, (memoryAccess slot).writeValue = none → (write w slot).value = (read w slot).value := effect.readonly

theorem main_partial_dependencies_retained : ¬ (Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.read (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 2) <
    Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 0)) :=
  Airbender.Tests.NativeWorkerSnapshot.main_partial_dependencies_retained

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerSnapshot.inactive_requests_retained

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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeJointReplay.Effects batch workers inputs :=
  NativeJointReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeJointReplay
