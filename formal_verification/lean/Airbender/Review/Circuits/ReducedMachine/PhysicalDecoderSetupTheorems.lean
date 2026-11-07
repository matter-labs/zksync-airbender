import Airbender.Proofs.ReducedMachine.NativePhysicalDecoderSetup

namespace Airbender.ReducedMachine.NativePhysicalDecoderSetup
open Native Trace NativeDecoderTableArguments

theorem constructed_decoder_setup {Kind R : Type} [Field R]
    (setup : SparseDecoderSetup Kind) (proof : Proof R) (i : Nat)
    (ordinary : i < decoderTableLayout.traceLength-1) :
    (withPublicSetup setup proof).main = proof.main ∧ setupQuery (withPublicSetup setup proof) i = ordinaryRow setup i :=
  ⟨rfl,(NativePhysicalDecoderSetupProofs.bound_decoder_query setup proof i).trans
    (NativePhysicalDecoderSetupProofs.normalized_ordinary setup i ordinary)⟩

theorem public_physical_decoder_source {w : Nat → F} {setup : SparseDecoderSetup UnifiedMode}
    {before : Reference.RiscV.Sail.State} {count : Nat} {fixed : Table F (fields 4)}
    (image : unifiedDecoderSetupImage before count 20 = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : (table setup).Contains #[] (decoderQuery w)) :
    sliceSize setup = decoderTableLayout.decoderCapacity ∧
      ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧ decoderQuery w = entry.query :=
  NativePhysicalDecoderSetupProofs.unified_source image holds member
/-- Acceptance is checked on the CONSTRUCTED public setup observations, not
    transferred from arbitrary observed setup data by an equality premise. -/
theorem same_main_constructed_decoder_setup {Kind Setup R : Type} [Field R]
    (setup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : NativeMemoryBoundary.PCChallenges R) (decoder : NativeDecoderArguments.Challenges R)
    (config : Airbender.Blake2Worker.Native.WorkerConfiguration Setup) {proofs : List (Proof R)}
    {batch : Airbender.Blake2Worker.Native.WorkerBatch Setup R} {inputs : NativeMemoryBoundary.PublicBoundary}
    {inverse : NativeMemoryBoundary.BoundaryInverses R}
    (accepted : NativeDecoderTableArguments.Accepted embed memory ch pc decoder config
      (proofs.map (withPublicSetup setup)) batch inputs inverse) :
    NativeMainArguments.Effects embed memory pc (proofs.map Proof.main) batch inputs ∧
      ∀ proof ∈ proofs, auxiliarySum proof true = auxiliarySum proof false ∧
        ∀ i < decoderTableLayout.traceLength-1, setupQuery (withPublicSetup setup proof) i = ordinaryRow setup i :=
  NativePhysicalDecoderSetupProofs.constructed_arguments setup embed memory ch pc decoder config accepted
end Airbender.ReducedMachine.NativePhysicalDecoderSetup
