import Airbender.Review.Circuits.ReducedMachine.MainDependenciesTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness
import Tests.NativeWorkerWriteWords

namespace Airbender.Tests.NativeMainDependencies
open Airbender.NativeMainDependencies
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem port_count : importedConstraintsMemoryPorts.size = 3 := by decide +kernel

theorem readonly_both (w : Nat → F) : writeWord w 0 = readWord w 0 ∧ writeWord w 1 = readWord w 1 :=
  ⟨NativeMainDependencyProofs.readonly_values w 0 (by decide +kernel),
   NativeMainDependencyProofs.readonly_values w 1 (by decide +kernel)⟩

theorem store_mask : wordMemoryMask true = 16386 := by decide +kernel

theorem store_values {w : Nat → F} (result : LocalEffects w)
    (observed : w 12 = (wordMemoryMask true : F)) : writeWord w 2 = readWord w 1 := result.store observed

/-- Reuse old complete LOCAL BODYs; these are not new global accepted witnesses. -/
theorem positive_local_both (active : Bool) : LocalEffects (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) :=
  native_main_value_dependencies (Airbender.ReducedMachine.NativeCSRPositiveWitness.body active)

/-- The second read may be the first port's same-row refresh. -/
theorem alias_refresh :
    (read (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 1).time =
      (write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 0).time := by decide +kernel

/-- A later old-read need not precede an earlier same-row write. -/
theorem alias_third : ¬ (Airbender.NativeCompleteMemoryPaths.rank
      (read (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 2) <
    Airbender.NativeCompleteMemoryPaths.rank (write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) 0)) := by
  decide +kernel

theorem native_write_ranks : (List.finRange 3).map
    (fun slot => Airbender.NativeCompleteMemoryPaths.rank (write (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment true) slot)) =
      [4,5,6] := by decide +kernel

theorem ordered_writes {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {row : MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) (a b : Fin 3) (earlier : a.val < b.val) :
    Airbender.NativeCompleteMemoryPaths.rank (write row.assignment a) <
      Airbender.NativeCompleteMemoryPaths.rank (write row.assignment b) := by
  rw [result.writes row member a,result.writes row member b]
  omega

theorem prefix_dependencies {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {row : MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) (a b : Fin 3) (earlier : a.val ≤ b.val) :
    Airbender.NativeCompleteMemoryPaths.rank (read row.assignment a) <
      Airbender.NativeCompleteMemoryPaths.rank (write row.assignment b) := result.before row member a b earlier

theorem all_last_dependencies {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {row : MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) : ∀ slot : Fin 3,
    Airbender.NativeCompleteMemoryPaths.rank (read row.assignment slot) <
      Airbender.NativeCompleteMemoryPaths.rank (write row.assignment 2) := by
  intro slot
  exact result.before row member slot 2 (by change slot.val ≤ 2; have := slot.isLt; omega)

theorem source_exact {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {row : MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) (slot : Fin 3) :
    read row.assignment slot ∈ Airbender.NativeLatestReads.available proofs batch := result.sources row member slot

theorem worker_retained {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) : Airbender.NativeWorkerWriteWords.Effects proofs batch inputs := result.workers

theorem inactive_retention {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.Tests.NativeWorkerWriteWords.inactive_read_retained proofs member zero slot

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeMainDependencyProofs.effects embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_main_read_dependencies embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeMainDependencies
