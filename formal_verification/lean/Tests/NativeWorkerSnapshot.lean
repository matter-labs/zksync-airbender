import Airbender.Review.Trace.Families.ReducedMachine.WorkerSnapshotTheorems
import Tests.NativeWorkerTransition
import Tests.NativeMainDependencies

namespace Airbender.Tests.NativeWorkerSnapshot
open Airbender.NativeWorkerSnapshot Airbender.NativeMixedReplay Airbender.Verification
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Small generic token data only, not a native/physical accepted worker. -/
private abbrev Cell := Nat × Nat
private def seeds : List Cell := [(0,0),(1,0)]
private def ports : List (Cell × Cell) := [((0,0),(0,3)),((1,0),(1,3))]
private def terminal : List Cell := [(1,3),(0,3)]

theorem equal_write_ranks : ports.Pairwise (fun a b => a.2.2 ≤ b.2.2) := by decide +kernel

theorem tied_replay : Replay Prod.fst seeds ports terminal := by
  refine .step (by decide +kernel) (.refl _) rfl ?_
  refine .step (by decide +kernel) ?_ rfl (.done (by decide +kernel) (.refl _))
  exact List.Perm.swap _ _ []

theorem second_read_common_seed : (1,0) ∈ seeds := by
  exact Airbender.NativeWorkerSnapshotProofs.early_read Prod.fst Prod.snd 3 (write := (1,3)) tied_replay
    (by intro edge member; simp [ports] at member; rcases member with rfl | rfl <;> decide +kernel)
    (by simp [ports]) (by decide +kernel)

theorem tied_cut : ∃ prior suffix, ports = prior ++ suffix ∧
    (∀ edge ∈ prior, edge.2.2 < 3) ∧ (∀ edge ∈ suffix, 3 ≤ edge.2.2) :=
  Airbender.NativeWorkerSnapshotProofs.ordered_cut (fun edge => edge.2.2) ports 3 equal_write_ranks

theorem duplicate_seed_rejected {edges : List (Cell × Cell)} {last : List Cell} :
    ¬ Replay Prod.fst [(0,0),(0,1)] edges last := by
  intro run
  have unique := Airbender.NativeMixedReplayProofs.initial_unique Prod.fst run
  simp at unique

theorem old_read_not_new : (1,0) ≠ (1,3) ∧ ¬ (3 < (3 : Nat)) := by decide +kernel

theorem decoded_actual_inputs (w : Nat → F) :
    sampledInput (read w) = Airbender.NativeWorkerTransition.readInput w :=
  Airbender.NativeWorkerSnapshotProofs.sampled_input w

section
variable {Setup R : Type} [Field R]
variable {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
variable {inputs : PublicBoundary} {w : Nat → F} {state : List Token}
variable (e : AtSnapshot proofs workers inputs w state)
include e

theorem all43_reads (slot : Fin 43) : read w slot ∈ state := e.reads slot

theorem exact_raw_token (slot : Fin 43) (token : Token) (present : token ∈ state)
    (same : token.address = (read w slot).address) : token = read w slot := e.exact slot token present same

theorem snapshot_reference (samples : Fin 43 → Token)
    (present : ∀ slot, samples slot ∈ state ∧ (samples slot).address = (read w slot).address) :
    Airbender.NativeWorkerTransition.observed w = Airbender.NativeWorkerTransition.transition (sampledInput samples) := by
  rw [e.sampled samples present]
  exact e.result

theorem all_state_outputs (samples : Fin 43 → Token)
    (present : ∀ slot, samples slot ∈ state ∧ (samples slot).address = (read w slot).address) :
    (Airbender.NativeWorkerTransition.observed w).state =
      (Airbender.NativeWorkerTransition.transition (sampledInput samples)).state :=
  congrArg Airbender.NativeWorkerTransition.Output.state (snapshot_reference e samples present)

theorem all_extended_outputs (samples : Fin 43 → Token)
    (present : ∀ slot, samples slot ∈ state ∧ (samples slot).address = (read w slot).address) :
    (Airbender.NativeWorkerTransition.observed w).extended =
      (Airbender.NativeWorkerTransition.transition (sampledInput samples)).extended :=
  congrArg Airbender.NativeWorkerTransition.Output.extended (snapshot_reference e samples present)

theorem both_control_outputs : (Airbender.NativeWorkerTransition.observed w).controlLow = 0 ∧
    (Airbender.NativeWorkerTransition.observed w).controlHigh = Airbender.NativeWorkerSchedule.nextHigh (w 135).val := by
  rw [e.result]
  exact ⟨rfl,rfl⟩

theorem unique_addresses : Function.Injective (fun slot : Fin 43 => (write w slot).address) := e.addresses

theorem both_raw_times (slot : Fin 43) : (write w slot).time = (write w 0).time := e.commonTime slot

theorem initialized_cut : Cut proofs workers inputs (Airbender.NativeCompleteMemoryPaths.rank (write w 0)) state := e.cut
end

/-- Reuse the existing MAIN alias counterexample; worker cuts do not strengthen MAIN dependencies. -/
theorem main_partial_dependencies_retained : ¬ (Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.read (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 2) <
    Airbender.NativeCompleteMemoryPaths.rank
      (Airbender.NativeMainDependencies.write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 0)) :=
  Airbender.Tests.NativeMainDependencies.alias_third

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerTransition.inactive_requests_retained

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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeWorkerSnapshot.Effects batch workers inputs :=
  native_counted_worker_snapshot publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerSnapshot
