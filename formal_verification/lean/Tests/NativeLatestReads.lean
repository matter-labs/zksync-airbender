import Airbender.Review.Circuits.ReducedMachine.LatestReadsTheorems
import Tests.NativeMemoryWriteUniqueness

namespace Airbender.Tests.NativeLatestReads
open Airbender.NativeLatestReads
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure path controls, not accepted native/source/physical witnesses. -/
private theorem chain (candidate : Nat) (member : candidate ∈ [0,3,5]) :
    (candidate < 5 → candidate ≤ 3) ∧ (candidate = 3 → candidate = 3) :=
  Airbender.NativeLatestReadsProofs.path_latest id
    (path := [0,3,5]) (edge := (3,5)) (by decide +kernel) (by decide +kernel) (by decide +kernel) member

theorem prior_candidate : (0 : Nat) ≤ 3 := (chain 0 (by decide +kernel)).1 (by decide +kernel)

theorem exact_predecessor : (3 : Nat) = 3 := (chain 3 (by decide +kernel)).2 rfl

theorem terminal_not_before_write : ¬ ((5 : Nat) < 5) := by decide +kernel

theorem gap_candidate_not_available : (4 : Nat) ∉ [0,3,5] := by decide +kernel

theorem repeated_rank_not_ordered : ¬ ([(0,7),(0,9)] : List (Nat × Nat)).Pairwise
    (fun left right => left.1 < right.1) := by decide +kernel

theorem changing_values :
    ((2 : Nat) < 4 → 2 ≤ 2) ∧ (2 = 2 → ((2,9) : Nat × Nat) = (2,9)) :=
  Airbender.NativeLatestReadsProofs.path_latest Prod.fst (candidate := (2,9))
    (path := [(0,0),(2,9),(4,11)]) (edge := ((2,9),(4,11)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem actual_initial_candidate (candidate : Nat) (member : candidate ∈ [0]) : candidate ∈ [0,3,5] := by
  have preserved : ∀ edge ∈ ([(0,3),(3,5)] : List (Nat × Nat)), (0 : Nat) = 0 := by intros; rfl
  exact Airbender.NativeLatestReadsProofs.on_path (fun _ : Nat => (0 : Nat))
    (initial := [0]) (steps := [(0,3),(3,5)]) (source := 0) (path := [0,3,5])
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) preserved
    (List.mem_append_left _ member) rfl

theorem actual_write_candidate (candidate : Nat) (member : candidate ∈ [3,5]) : candidate ∈ [0,3,5] := by
  have preserved : ∀ edge ∈ ([(0,3),(3,5)] : List (Nat × Nat)), (0 : Nat) = 0 := by intros; rfl
  exact Airbender.NativeLatestReadsProofs.on_path (fun _ : Nat => (0 : Nat))
    (initial := [0]) (steps := [(0,3),(3,5)]) (source := 0) (path := [0,3,5])
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) preserved
    (List.mem_append_right _ member) rfl

theorem oldread_source {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {read write : Token}
    (actual : Airbender.NativeMixedMemoryOrder.Step proofs batch read write) : read ∈ available proofs batch :=
  (result.reads read write actual).source

theorem exact_oldread_value {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {read write candidate : Token}
    (actual : Airbender.NativeMixedMemoryOrder.Step proofs batch read write)
    (member : candidate ∈ available proofs batch) (address : candidate.address = read.address)
    (rankEq : Airbender.NativeCompleteMemoryPaths.rank candidate = Airbender.NativeCompleteMemoryPaths.rank read) :
    candidate.value = read.value := congrArg Trace.MemoryToken.value ((result.reads read write actual).exact candidate member address rankEq)

theorem all43_worker_latest {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (active : w constraintsABI.multiplicity = 1)
    (slot : Fin 43) : Latest proofs batch (Airbender.NativeWorkerClockProgress.readToken w slot)
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) :=
  result.reads _ _ (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)

theorem inactive_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.Tests.NativeMemoryWriteUniqueness.inactive_read_retained proofs member zero slot

theorem zero_factor_retained : memoryKeyArgument (RingHom.id F) ⟨0,0,0,0,0,0,0⟩
    ⟨⟨0,4,0⟩,#v[0,0],#v[0,0]⟩ = 0 := Airbender.Tests.NativeMemoryWriteUniqueness.zero_factor_retained

theorem all32_register_seeds : Airbender.NativeInitializationSeedBoundary.initialRegisters.length = 32 :=
  Airbender.Tests.NativeCompleteMemoryPaths.all32_register_seeds

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeLatestReadsProofs.effects embed memory ch pc gamma config accepted identity

/-- Positive main count, every prefix guard and full prior acceptance stay
    coupled to these exact latest-read observations. Clean/Sail history stays separate. -/
theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeLatestReadsProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeLatestReads
