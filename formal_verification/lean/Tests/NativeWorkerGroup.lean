import Airbender.Review.Trace.Families.ReducedMachine.WorkerGroupTheorems
import Tests.NativeWorkerSnapshot

namespace Airbender.Tests.NativeWorkerGroup
open Airbender.NativeWorkerGroup Airbender.NativeWorkerSnapshot Airbender.NativeMixedReplay
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic small tokens only, not native or physical accepted worker witnesses. -/
private abbrev Cell := Nat × Nat
private def seeds : List Cell := [(0,0),(1,0),(2,0),(9,11)]
private def group : List (Cell × Cell) := [((0,0),(0,3)),((1,0),(1,3))]
private def edges : List (Cell × Cell) := ((2,0),(2,3)) :: group
private def terminal : List Cell := [(0,3),(1,3),(2,3),(9,11)]

theorem equal_rank_original_replay : Replay Prod.fst seeds edges terminal := by
  apply Airbender.NativeMixedReplayProofs.replay_sorted Prod.fst Prod.snd edges seeds terminal
  · decide +kernel
  · decide +kernel
  · intro edge member
    simp only [edges,group,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro edge member
    simp only [edges,group,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel
  · decide +kernel

theorem regrouped_ties : ∃ post rest, edges.Perm (group ++ rest) ∧ Replay Prod.fst seeds group post ∧
    Replay Prod.fst post rest terminal ∧ rest.Pairwise (fun a b => a.2.2 ≤ b.2.2) ∧
    (∀ edge ∈ rest, 3 ≤ edge.2.2) := by
  apply Airbender.NativeWorkerGroupProofs.regroup Prod.fst Prod.snd 3 group equal_rank_original_replay
  · decide +kernel
  · intro edge member
    exact List.mem_cons_of_mem _ member
  · intro edge member
    simp only [group,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · intro edge member
    simp only [edges,group,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro edge member
    simp only [edges,group,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel
  · intro edge member
    simp only [edges,group,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel

theorem other_tied_edge_retained {rest : List (Cell × Cell)} (same : edges.Perm (group ++ rest)) :
    ((2,0),(2,3)) ∈ rest := by
  have member := same.mem_iff.mp (show ((2,0),(2,3)) ∈ edges by simp [edges])
  simpa [group] using member

theorem frame_at_other_tied_address {post : List Cell} (run : Replay Prod.fst seeds group post) : (2,0) ∈ post := by
  apply (Airbender.NativeWorkerGroupProofs.frame Prod.fst run (2,0) ?_).mpr (by simp [seeds])
  intro edge member
  simp only [group,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

theorem frame_at_unused_address {post : List Cell} (run : Replay Prod.fst seeds group post) : (9,11) ∈ post := by
  apply (Airbender.NativeWorkerGroupProofs.frame Prod.fst run (9,11) ?_).mpr (by simp [seeds])
  intro edge member
  simp only [group,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

theorem both_group_writes {post : List Cell} (run : Replay Prod.fst seeds group post) :
    (0,3) ∈ post ∧ (1,3) ∈ post := by
  have written := Airbender.NativeWorkerGroupProofs.writes_present Prod.fst run (by decide +kernel)
  exact ⟨written ((0,0),(0,3)) (by simp [group]),written ((1,0),(1,3)) (by simp [group])⟩

theorem duplicate_address_group_rejected :
    ¬ (([((0,0),(0,3)),((0,0),(0,3))] : List (Cell × Cell)).map (fun edge => edge.1.1)).Nodup := by decide +kernel

theorem actual_post_output_decode (w : Nat → F) :
    sampledOutput (write w) = Airbender.NativeWorkerTransition.observed w := NativeWorkerGroupProofs.sampled_output w

section
variable {Setup R : Type} [Field R]
variable {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
variable {inputs : PublicBoundary} {w : Nat → F} {before after : List Token}
variable (e : Airbender.NativeWorkerGroup.RowEffects proofs workers inputs w before after)
include e

theorem all43_post_writes (slot : Fin 43) : write w slot ∈ after := e.writes slot

theorem exact_post_token (slot : Fin 43) (token : Token) (present : token ∈ after)
    (same : token.address = (write w slot).address) : token = write w slot := e.exact slot token present same

theorem unaffected_frame (token : Token) (outside : ∀ slot, token.address ≠ (write w slot).address) :
    (token ∈ after ↔ token ∈ before) := e.frame token outside

theorem both_snapshot_reference (old fresh : Fin 43 → Token)
    (oldPresent : ∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address)
    (freshPresent : ∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) :
    sampledOutput fresh = Airbender.NativeWorkerTransition.transition (sampledInput old) := e.reference old fresh oldPresent freshPresent

theorem all_state_results (old fresh : Fin 43 → Token)
    (oldPresent : ∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address)
    (freshPresent : ∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) :
    (sampledOutput fresh).state = (Airbender.NativeWorkerTransition.transition (sampledInput old)).state :=
  congrArg Airbender.NativeWorkerTransition.Output.state (e.reference old fresh oldPresent freshPresent)

theorem all_extended_results (old fresh : Fin 43 → Token)
    (oldPresent : ∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address)
    (freshPresent : ∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) :
    (sampledOutput fresh).extended = (Airbender.NativeWorkerTransition.transition (sampledInput old)).extended :=
  congrArg Airbender.NativeWorkerTransition.Output.extended (e.reference old fresh oldPresent freshPresent)

theorem readonly_refresh_values (slot : Fin 43) (readonly : (memoryAccess slot).writeValue = none) :
    (write w slot).value = (read w slot).value := e.readonly slot readonly

theorem complete_residual_replay : Segment proofs workers inputs w before after := e.segment
end

theorem main_partial_dependencies_retained : ¬ (Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.read (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 2) <
    Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 0)) :=
  Airbender.Tests.NativeWorkerSnapshot.main_partial_dependencies_retained

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerSnapshot.inactive_requests_retained

theorem complete_counted {Setup R : Type} [Field R]
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeWorkerGroup.Effects batch workers inputs :=
  native_counted_worker_group publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerGroup
