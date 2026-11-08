import Airbender.Review.Circuits.ReducedMachine.MainDecoder
import Airbender.Proofs.ReducedMachine.NativeMainBatch
import Airbender.Proofs.ReducedMachine.NativePhysicalDecoderSetup

namespace Airbender.NativeMainDecoderProofs
open Airbender.NativeMainDecoder
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Airbender.Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Entire list composition before native proof/domain instantiation. -/
theorem mapped_views {A B C D : Type} (items : List A) (first : A → B) (second : A → C)
    (left : B → D) (right : C → D) (same : ∀ item, left (first item) = right (second item)) :
    (items.map first).map left = (items.map second).map right := by
  simp only [List.map_map]
  exact List.map_congr_left fun item _ => same item

theorem main_list {R : Type} [Field R] (batch : Batch R) :
    batch.main.proofs = batch.proofs.map Proof.initialization := by
  simp only [Batch.main,Airbender.NativeMainBatch.Batch.proofs,Batch.proofs,Vector.toList_map]

theorem count_binding {R : Type} [Field R] (batch : Batch R) : batch.proofs.length = batch.countWord.toNat := by
  simp only [Batch.proofs,Vector.length_toList]

theorem decoder_main {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (proof : Proof R) :
    (Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder).main =
      proof.initialization.main := rfl

theorem same_main_list {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (batch : Batch R) :
    (batch.decoder publicSetup).map Airbender.ReducedMachine.NativeDecoderTableArguments.Proof.main =
      Airbender.NativeInitializationBatch.mainArguments batch.main.proofs := by
  rw [main_list]
  exact mapped_views batch.proofs
    (fun proof => Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder)
    Proof.initialization Airbender.ReducedMachine.NativeDecoderTableArguments.Proof.main
    Airbender.NativeInitializationBatch.Proof.main (decoder_main publicSetup)

theorem decoder_accepted {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse) :
    Airbender.ReducedMachine.NativeDecoderTableArguments.Accepted embed memory ch pc decoder config
      (batch.decoder publicSetup) workers inputs inverse := by
  constructor
  · constructor
    · rw [same_main_list]
      exact accepted.counted.component.arguments
    · intro main member i ordinary
      obtain ⟨view,present,rfl⟩ := List.mem_map.mp member
      obtain ⟨proof,source,rfl⟩ := List.mem_map.mp present
      exact accepted.access proof source i ordinary
  · intro view member
    obtain ⟨proof,source,rfl⟩ := List.mem_map.mp member
    exact accepted.tables proof source

theorem decoder_effects {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse) :
    DecoderEffects publicSetup embed decoder batch := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro proof member i ordinary
    exact Airbender.ReducedMachine.NativeDecoderArgumentProofs.row_equation embed decoder (accepted.access proof member i ordinary)
  · intro proof member
    have sum := Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.auxiliary_sum embed decoder (accepted.tables proof member)
    exact sum
  · intro proof member
    exact Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.polynomial_zero embed decoder (accepted.tables proof member)
  · intro proof member
    exact Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.last_auxiliaries embed decoder (accepted.tables proof member)
  · intro proof _ i ordinary
    exact (Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs.bound_decoder_query publicSetup proof.decoder i).trans
      (Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs.normalized_ordinary publicSetup i ordinary)

/-- Generic fetched-source extraction; no native data or large domain unfolds. -/
theorem public_source {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count : Nat} {publicSetup : SparseDecoderSetup Kind}
    {w : Nat → F}
    (image : sparseDecoderSetupImageRunWith projection before count 20 = some publicSetup)
    (body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (member : (Airbender.ReducedMachine.NativePhysicalDecoderSetup.table publicSetup).Contains #[] (decoderQuery w)) :
    ∃ entry ∈ publicSetup.program, entry.SourceWith before projection ∧ decoderQuery w = entry.query := by
  have logical := Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs.public_member member
    (Airbender.ReducedMachine.NativeShiftDecoderProofs.padding_excluded body)
  obtain ⟨entry,present,same⟩ := Airbender.Trace.Proofs.sparse_member logical
    (Airbender.ReducedMachine.NativeShiftDecoderProofs.padding_excluded body)
  exact ⟨entry,present,(Airbender.Trace.Proofs.run_sparse_setup_sources image present).1,same⟩

theorem public_sources {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {projection : SailRV32.instruction → Option (DecoderData Kind)} {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : sparseDecoderSetupImageRunWith projection before count 20 = some publicSetup)
    (lookups : LogicalLookups publicSetup batch) : PublicSources projection before publicSetup batch := by
  intro proof member i ordinary active
  exact public_source image (accepted.access proof member i ordinary).body (lookups proof member i ordinary active)

theorem joint {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse) :
    Airbender.NativeMainBatch.Effects batch.main ∧ DecoderEffects publicSetup embed decoder batch ∧
      Airbender.NativeWorkerClockProgress.Effects workers := by
  have previous := Airbender.NativeMainBatchProofs.joint embed memory ch pc gamma config accepted.counted
  exact ⟨previous.1,decoder_effects publicSetup embed memory ch pc gamma decoder config accepted,previous.2⟩
end Airbender.NativeMainDecoderProofs
