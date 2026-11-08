import Airbender.Proofs.ReducedMachine.NativeCallerDecoder

namespace Airbender.NativeCallerDecoder
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Valid original public fields determine the full CSR mask before using the
    runtime table. This does not assert activity or worker issuance. -/
theorem native_decoded_caller_request {w : Nat → F} {entry : Program}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : RowEffects w entry :=
  NativeCallerDecoderProofs.row holds fields query

/-- Same counted complete components and actual active public fetched sources.
    Inactive requests and crypto extraction boundaries remain explicit. -/
theorem native_counted_caller_requests {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Mode) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) :
    Airbender.NativeMainBatch.Effects batch.main ∧
      Airbender.NativeMainDecoder.DecoderEffects publicSetup embed decoder batch ∧
      Airbender.NativeWorkerClockProgress.Effects workers ∧ Effects before publicSetup batch :=
  NativeCallerDecoderProofs.joint publicSetup embed memory ch pc gamma decoder config accepted image lookups
end Airbender.NativeCallerDecoder
