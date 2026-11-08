import Airbender.Proofs.ReducedMachine.NativeMainDecoder

namespace Airbender.NativeMainDecoder
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Airbender.Trace

/-- Complete source components on the SAME counted main list and worker batch.
    Public setup authentication and cryptographic extraction remain separate. -/
theorem native_counted_main_decoder {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse) :
    Airbender.NativeMainBatch.Effects batch.main ∧ DecoderEffects publicSetup embed decoder batch ∧
      Airbender.NativeWorkerClockProgress.Effects workers :=
  NativeMainDecoderProofs.joint publicSetup embed memory ch pc gamma decoder config accepted

/-- All actual active physical queries recover original public decoded sources.
    Logical membership is named explicitly; no execution/retirement is asserted. -/
theorem native_counted_public_sources {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {projection : SailRV32.instruction → Option (DecoderData Kind)} {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : sparseDecoderSetupImageRunWith projection before count 20 = some publicSetup)
    (lookups : LogicalLookups publicSetup batch) : PublicSources projection before publicSetup batch :=
  NativeMainDecoderProofs.public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
end Airbender.NativeMainDecoder
