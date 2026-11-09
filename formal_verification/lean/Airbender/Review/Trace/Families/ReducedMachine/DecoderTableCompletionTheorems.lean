import Airbender.Proofs.ReducedMachine.NativeDecoderTableCompletion

namespace Airbender.NativeDecoderTableCompletion
/-- Complete decoder table equations, actual zero/last difference polynomial and
    constructed public setup share the SAME inactive request-positive main/caller
    component. No decoder nonpole is assumed. Primitive-domain construction,
    scalar/global source/worker completion and physical refinement remain open. -/
theorem native_inactive_decoder_table_completion : ∃ w, Fixture w :=
  NativeDecoderTableCompletionProofs.fixture
end Airbender.NativeDecoderTableCompletion
