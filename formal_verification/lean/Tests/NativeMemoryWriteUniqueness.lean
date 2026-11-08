import Airbender.Review.Circuits.ReducedMachine.MemoryWriteUniquenessTheorems
import Tests.NativeCompleteMemoryPaths

namespace Airbender.Tests.NativeMemoryWriteUniqueness
open Airbender.NativeMemoryWriteUniqueness
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure counted-list controls; not accepted native/source/physical witnesses. -/
theorem same_address_same_rank_rejected : ¬ ([(7,3),(7,3)] : List (Nat × Nat)).Nodup := by decide +kernel

theorem different_addresses_same_rank : ([(7,3),(8,3)] : List (Nat × Nat)).Nodup := by decide +kernel

theorem same_address_later_rank : ([(7,3),(7,4)] : List (Nat × Nat)).Nodup := by decide +kernel

theorem rank_alone_can_repeat : ¬ (([(7,3),(8,3)] : List (Nat × Nat)).map Prod.snd).Nodup := by decide +kernel

theorem grouped_chain : (([(7,3),(7,4),(8,3)] : List (Nat × Nat)).map fun x => (x.1,x.2)).Nodup := by
  apply Airbender.NativeMemoryWriteUniquenessProofs.grouped_nodup Prod.fst Prod.snd
  intro item member
  simp at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

theorem complete_chain_writes :
    (([(0,1),(1,2)] : List (Nat × Nat)).map fun edge => ((0 : Nat),edge.2)).Nodup := by
  have preserved : ∀ edge ∈ ([(0,1),(1,2)] : List (Nat × Nat)), (0 : Nat) = 0 := by intros; rfl
  have increases : ∀ edge ∈ ([(0,1),(1,2)] : List (Nat × Nat)), edge.1 < edge.2 := by
    intro edge member
    simp at member
    rcases member with rfl | rfl <;> decide +kernel
  exact Airbender.NativeMemoryWriteUniquenessProofs.unique_writes (fun _ : Nat => (0 : Nat)) id
    (initial := [0]) (terminal := [2]) (by decide +kernel) preserved (by decide +kernel) increases

theorem duplicate_segment_preserved : ([4,4] : List Nat).Sublist [1,4,4,9] := by
  have part := Airbender.NativeMemoryWriteUniquenessProofs.flatMap_segment
    (fun n : Nat => if n = 0 then [1] else if n = 1 then [4,4] else [9])
    (items := [0,1,2]) (item := 1) (by decide +kernel)
  exact part

theorem duplicate_segment_rejected : ¬ ([1,4,4,9] : List Nat).Nodup := by decide +kernel

theorem actual_writes_unique {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) :
    ((Airbender.NativeMemoryRoots.steps proofs batch).map fun edge => writeKey edge.2).Nodup := result.writes

theorem worker_slot_identity {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (active : w constraintsABI.multiplicity = 1)
    {left right : Fin 43} (same : (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w left true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w right true)).address) : left = right :=
  result.workerAddresses w member active same

theorem worker_alias_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (active : w constraintsABI.multiplicity = 1)
    {left right : Fin 43} (different : left ≠ right)
    (same : (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w left true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w right true)).address) : False :=
  different (result.workerAddresses w member active same)

theorem all43_addresses_unique {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (active : w constraintsABI.multiplicity = 1) :
    ((List.finRange 43).map fun slot =>
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).address).Nodup :=
  (List.nodup_finRange 43).map (result.workerAddresses w member active)

theorem inactive_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.Tests.NativeCompleteMemoryPaths.inactive_source_read_stays proofs member zero slot

theorem zero_factor_retained : memoryKeyArgument (RingHom.id F) ⟨0,0,0,0,0,0,0⟩
    ⟨⟨0,4,0⟩,#v[0,0],#v[0,0]⟩ = 0 := Airbender.Tests.NativeCompleteMemoryPaths.zero_factor_retained

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeMemoryWriteUniquenessProofs.effects embed memory ch pc gamma config accepted identity

/-- Positive main count, every prefix guard and full prior acceptance stay
    coupled to these exact writes and worker ports. Clean/Sail history stays separate. -/
theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeMemoryWriteUniquenessProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeMemoryWriteUniqueness
