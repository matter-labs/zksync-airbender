import Airbender.Review.Circuits.ReducedMachine.MainDecoderTheorems
import Airbender.Review.Circuits.ReducedMachine.CSRDecoder

namespace Airbender.Tests.NativeMainDecoder
open Airbender.NativeMainDecoder
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Airbender.Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Structural DATA controls do not supply accepted nonempty source proofs. -/
theorem count_binding {R : Type} [Field R] (batch : Batch R) : batch.proofs.length = batch.countWord.toNat :=
  Airbender.NativeMainDecoderProofs.count_binding batch

theorem same_main {R : Type} [Field R] (proof : Proof R) : proof.decoder.main = proof.initialization.main := rfl

theorem same_rows {R : Type} [Field R] (proof : Proof R) :
    proof.decoder.main.memory.rows = proof.initialization.main.memory.rows := rfl

theorem same_auxiliary {R : Type} [Field R] (proof : Proof R) :
    proof.decoder.main.memory.auxiliary = proof.initialization.main.memory.auxiliary := rfl

theorem witness_preserved {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (proof : Proof R) :
    (Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder).witness = proof.witness := rfl

theorem other_setup_preserved {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (proof : Proof R)
    (i : Nat) (column : DecoderSetupColumn)
    (outside : ¬ (decoderTableLayout.setupStart ≤ column.index ∧ column.index < decoderTableLayout.setupStart+10)) :
    (Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder).setup i column = proof.setup i column :=
  Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs.bound_other_columns publicSetup proof.decoder i column outside

theorem ordinary_setup_binding {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (proof : Proof R)
    (i : Nat) (ordinary : i < decoderTableLayout.traceLength-1) :
    Airbender.ReducedMachine.NativeDecoderTableArguments.setupQuery
      (Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder) i =
        Airbender.ReducedMachine.NativePhysicalDecoderSetup.ordinaryRow publicSetup i :=
  (Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs.bound_decoder_query publicSetup proof.decoder i).trans
    (Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs.normalized_ordinary publicSetup i ordinary)

theorem same_actual_list {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (batch : Batch R) :
    (batch.decoder publicSetup).map Airbender.ReducedMachine.NativeDecoderTableArguments.Proof.main =
      Airbender.NativeInitializationBatch.mainArguments batch.main.proofs :=
  Airbender.NativeMainDecoderProofs.same_main_list publicSetup batch

theorem decoder_positions_preserved {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (batch : Batch R) :
    (batch.decoder publicSetup).length = batch.countWord.toNat := by
  rw [Batch.decoder,List.length_map,Airbender.NativeMainDecoderProofs.count_binding]

theorem duplicate_views_preserved {R : Type} [Field R] (proof : Proof R) :
    [proof,proof].map Proof.initialization = [proof.initialization,proof.initialization] := rfl

private def emptyBatch (R : Type) [Field R] : Batch R := ⟨0,#v[]⟩

theorem empty_lookups {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) :
    LogicalLookups publicSetup (emptyBatch R) := by
  intro proof member
  change proof ∈ ([] : List (Proof R)) at member
  cases member

theorem empty_counter_rejected {R : Type} [Field R] :
    ¬ Airbender.NativeMainBatch.CounterAccepted (emptyBatch R).main := by
  rw [Airbender.NativeMainBatchProofs.counter_iff]
  change ¬ ((0 : Nat) < 0 ∧ 0 ≤ 8192)
  decide +kernel

theorem complete_conditional_joint {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse) :
    Airbender.NativeMainBatch.Effects batch.main ∧ DecoderEffects publicSetup embed decoder batch ∧
      Airbender.NativeWorkerClockProgress.Effects workers :=
  native_counted_main_decoder publicSetup embed memory ch pc gamma decoder config accepted

theorem complete_conditional_csr_source {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup CSRMode) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : csrDecoderSetupImage before count 20 = some publicSetup)
    (lookups : LogicalLookups publicSetup batch) : PublicSources csrDecoderFields before publicSetup batch :=
  native_counted_public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
end Airbender.Tests.NativeMainDecoder
