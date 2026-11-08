import Airbender.Review.Circuits.ReducedMachine.MemoryRootsTheorems

namespace Airbender.Tests.NativeMemoryRoots
open Airbender.NativeMemoryRoots
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure list controls, not native source/physical accepted witnesses. -/
theorem duplicate_cancellation :
    ([0,1,7,7] : List Nat).Perm [1,0,7,7] ↔ ([0,1] : List Nat).Perm [1,0] :=
  Airbender.NativeMemoryRootsProofs.cancel [0] [1] [1,7,7] [0,7,7] [1] [0] [7,7]
    (List.Perm.refl _) (List.Perm.refl _)

theorem duplicate_restoration : ([0,1,7,7] : List Nat).Perm [1,0,7,7] :=
  duplicate_cancellation.mpr (by decide +kernel)

theorem inactive_only_common :
    ([7,7] : List Nat).Perm [7,7] ↔ ([] : List Nat).Perm [] :=
  Airbender.NativeMemoryRootsProofs.cancel [] [] [7,7] [7,7] [] [] [7,7]
    (List.Perm.refl _) (List.Perm.refl _)

private theorem small_roots (initial terminal : List Nat) (edges : List (Nat × Nat))
    (matching : (initial ++ edges.map Prod.snd).Perm (terminal ++ edges.map Prod.fst))
    (strict : ∀ edge ∈ edges, edge.1 < edge.2) :
    ∀ token ∈ edges.map Prod.fst, ∃ seed ∈ initial,
      Relation.ReflTransGen (fun a b => (a,b) ∈ edges) seed token :=
  Airbender.NativeMemoryRootsProofs.rooted initial terminal edges id matching strict

theorem two_step_seed_path : ∃ seed ∈ [0],
    Relation.ReflTransGen (fun a b : Nat => (a,b) ∈ [(0,1),(1,2)]) seed 1 := by
  apply small_roots [0] [2] [(0,1),(1,2)] (by decide +kernel) _ 1 (by decide +kernel)
  intro edge member
  simp at member
  rcases member with rfl | rfl <;> decide +kernel

theorem separate_seed_paths : ∃ seed ∈ [0,10],
    Relation.ReflTransGen (fun a b : Nat => (a,b) ∈ [(0,1),(1,2),(10,11)]) seed 10 := by
  apply small_roots [0,10] [2,11] [(0,1),(1,2),(10,11)] (by decide +kernel) _ 10 (by decide +kernel)
  intro edge member
  simp at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

/-- Duplicates are preserved; seed paths alone are not uniqueness. -/
theorem duplicate_active_paths : ∃ seed ∈ [0,0],
    Relation.ReflTransGen (fun a b : Nat => (a,b) ∈ [(0,1),(0,1)]) seed 0 := by
  apply small_roots [0,0] [1,1] [(0,1),(0,1)] (by decide +kernel) _ 0 (by decide +kernel)
  intro edge member
  simp at member
  rcases member with rfl; decide +kernel

/-- A matching self-loop without seeds remains possible as pure data; strict
    active order rejects it, so cancellation is needed before rooting. -/
theorem unseeded_loop_matching : ([] ++ [7] : List Nat).Perm ([] ++ [7]) := List.Perm.refl _

theorem unseeded_loop_not_strict (rank : Nat → Nat) : ¬ rank 7 < rank 7 := Nat.lt_irrefl _

theorem all_worker_positions (w : Nat → F) : (workerSteps w).length = 43 := by
  simp [workerSteps]

theorem inactive_exact_tokens {w : Nat → F} (accepted : LocalProcessingAccepted w)
    (zero : w constraintsABI.multiplicity = 0) :
    Airbender.NativeMemoryTokens.workerTokens w true = Airbender.NativeMemoryTokens.workerTokens w false :=
  Airbender.NativeMemoryRootsProofs.inactive_equal accepted zero

theorem inactive_source_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  ⟨zero,Airbender.NativeWorkerClockProgressProofs.read_member proofs member slot⟩

theorem active_edge_list_exact {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) (read write : Token) :
    (read,write) ∈ steps proofs batch ↔ Airbender.NativeMixedMemoryOrder.Step proofs batch read write :=
  Airbender.NativeMemoryRootsProofs.step_iff proofs batch read write

theorem actual_main_read_root {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs)
    {port : Trace.MemoryPort} (actual : port ∈ row.ports) :
    ∃ seed ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
      Relation.ReflTransGen (Airbender.NativeMixedMemoryOrder.Step proofs batch) seed (Trace.readToken row.assignment port) :=
  result.reads _ _ (Or.inl ⟨row,member,port,actual,rfl,rfl⟩)

theorem actual_worker_write_root {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) (slot : Fin 43) :
    ∃ seed ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
      Relation.ReflTransGen (Airbender.NativeMixedMemoryOrder.Step proofs batch) seed
        (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) :=
  result.writes _ _ (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  native_memory_seed_paths embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_memory_seed_paths embed memory ch pc gamma config accepted identity

end Airbender.Tests.NativeMemoryRoots
