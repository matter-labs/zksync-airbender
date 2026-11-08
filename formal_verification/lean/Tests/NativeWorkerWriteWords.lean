import Airbender.Review.Circuits.ReducedMachine.WorkerWriteWordsTheorems
import Tests.NativeWorkerWriteSlices

namespace Airbender.Tests.NativeWorkerWriteWords
open Airbender.NativeWorkerWriteWords
open Airbender.NativeWorkerWriteSlices (WordBound PortEffect)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Finite metadata and conditional controls, not new global accepted witnesses. -/
theorem arithmetic_slots : ([9,10,11,12,17,18,19,20] : List Nat).length = 8 := by decide +kernel

theorem all43_retained : (List.finRange 43).length = 43 := by simp

theorem low7_high9_endpoint : ((127 : F)+128*511).val = 65535 := by decide +kernel

theorem low8_high8_endpoint : ((255 : F)+256*255).val = 65535 := by decide +kernel

theorem arithmetic_first {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    WordBound (keyValue w 9 true) :=
  NativeWorkerWriteWordProofs.arithmetic_ports accepted 0

theorem arithmetic_last {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    WordBound (keyValue w 20 true) :=
  NativeWorkerWriteWordProofs.arithmetic_ports accepted 7

theorem wide_arithmetic_rejected {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (wide : w 38 = 65536) : False := by
  have bound := NativeWorkerWriteWordProofs.arithmetic_words accepted 0
  change (w 38).val < 65536 at bound
  rw [wide] at bound
  exact (by decide +kernel : ¬ ((65536 : F).val < 65536)) bound

theorem negative_carry_rejected {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (wide : w 70 = -65536) : False := by
  have bound := NativeWorkerWriteWordProofs.arithmetic_words accepted 8
  change (w 70).val < 65536 at bound
  rw [wide] at bound
  exact (by decide +kernel : ¬ ((-65536 : F).val < 65536)) bound

theorem complete_positive_body : LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_write_words Airbender.Blake2Worker.PositiveRowProofs.body

theorem prior35_retained {w : Nat → F} (result : LocalEffects w) :
    Airbender.NativeWorkerWriteSlices.LocalEffects w := result.slices

theorem all43_observations {w : Nat → F} (result : LocalEffects w) (slot : Fin 43) :
    WordBound (keyValue w slot true) ∨ keyValue w slot true = keyValue w slot false := result.ports slot

theorem copied_value_needs_bound : ¬ WordBound #v[(65536 : F),0] :=
  Airbender.Tests.NativeWorkerWriteSlices.wide_limb_not_word

theorem internal_preservation {w : Nat → F} (result : LocalEffects w)
    (reads : ∀ slot, WordBound (keyValue w slot false)) :
    ∀ slot, WordBound (keyValue w slot true) := NativeWorkerWriteWordProofs.preserves result reads

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
  Airbender.Tests.NativeWorkerWriteSlices.inactive_read_retained proofs member zero slot

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_worker_write_words embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeWorkerWriteWords
