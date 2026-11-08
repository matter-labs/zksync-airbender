import Airbender.Review.Circuits.ReducedMachine.WorkerWriteSlicesTheorems
import Airbender.Proofs.Blake2Worker.NativePositiveRow
import Tests.NativeLatestReads

namespace Airbender.Tests.NativeWorkerWriteSlices
open Airbender.NativeWorkerWriteSlices
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private instance coveredDecidable (slot : Fin 43) : Decidable (Covered slot) := by
  unfold Covered
  infer_instance

/-- Finite metadata/reference controls, not global accepted worker witnesses. -/
theorem covered_count : ((List.finRange 43).filter fun slot => decide (Covered slot)).length = 35 := by
  unfold Covered
  decide +kernel

theorem uncovered_exact (slot : Fin 43) : ¬ Covered slot ↔ slot.val ∈ [9,10,11,12,17,18,19,20] := by
  fin_cases slot <;> unfold Covered <;> decide +kernel

theorem all43_retained : (List.finRange 43).length = 43 := by simp

theorem readonly_gpr (w : Nat → F) : keyValue w 0 true = keyValue w 0 false :=
  NativeWorkerWriteSliceProofs.readonly_values w 0 (by decide +kernel)

theorem readonly_messages (w : Nat → F) (index : Fin 16) :
    keyValue w ⟨26 + index.val,by have := index.isLt; omega⟩ true =
      keyValue w ⟨26 + index.val,by have := index.isLt; omega⟩ false :=
  NativeWorkerWriteSliceProofs.readonly_values w _ (by
    change 26 + index.val = 0 ∨ (25 ≤ 26 + index.val ∧ 26 + index.val < 42)
    have := index.isLt
    omega)

theorem radix128_max : ((127 : F)+128*511).val < 65536 :=
  NativeWorkerWriteSliceProofs.reconstruct 127 511 128 (by decide +kernel)

theorem radix512_max : ((511 : F)+512*127).val < 65536 :=
  NativeWorkerWriteSliceProofs.reconstruct 511 127 512 (by decide +kernel)

theorem radix256_max : ((255 : F)+256*255).val < 65536 :=
  NativeWorkerWriteSliceProofs.reconstruct 255 255 256 (by decide +kernel)

theorem wide_limb_not_word : ¬ WordBound #v[(65536 : F),0] := by
  intro bounded
  have low := bounded 0
  change (65536 : F).val < 65536 at low
  exact (by decide +kernel : ¬ ((65536 : F).val < 65536)) low

theorem complete_positive_body : LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_write_slices Airbender.Blake2Worker.PositiveRowProofs.body

theorem derived_finalization_bit {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    w 152 = 0 ∨ w 152 = 1 := (native_worker_write_slices accepted).finalization

theorem covered_write_observation {w : Nat → F} (result : LocalEffects w) (slot : Fin 43) (covered : Covered slot) :
    WordBound (keyValue w slot true) ∨ keyValue w slot true = keyValue w slot false := result.ports slot covered

theorem all_actual_workers {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) : LocalEffects w := result.workers w member

theorem inactive_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.Tests.NativeLatestReads.inactive_read_retained proofs member zero slot

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeWorkerWriteSliceProofs.effects embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_worker_write_slices embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeWorkerWriteSlices
