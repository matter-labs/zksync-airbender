import Airbender.Proofs.ReducedMachine.NativeTokenLedger

namespace Airbender.NativeTokenLedger
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native

/-- Complete native auxiliary acceptance gives scalar product balance on these
    exact full-domain tokens. It does not establish LogicalMatching. -/
theorem native_full_token_products {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R) (pc : PCChallenges R)
    (config : WorkerConfiguration Setup) {mains : List (MainProof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed memory processor pc config mains batch inputs inverse) :
    ((fullTokens mains batch inputs true).map (argument embed memory pc)).prod =
      ((fullTokens mains batch inputs false).map (argument embed memory pc)).prod :=
  NativeTokenLedgerProofs.accepted_product_balance embed memory processor pc config accepted

/-- Faithful filtering at the explicit precompression logical boundary. No
    caller request is filtered, and inactive compressed factors are never divided. -/
theorem native_logical_active_matching {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    LogicalMatching mains batch inputs ↔
      (activeTokens mains batch inputs true).Perm (activeTokens mains batch inputs false) :=
  NativeTokenLedgerProofs.matching_iff mains batch inputs

/-- Exact memory and PC/state matching follow by observing the tagged logical
    ledger. This supplies no chronological history, initialized values or range. -/
theorem native_memory_state_matching {Setup R : Type} [Field R] {mains : List (MainProof R)}
    {batch : WorkerBatch Setup R} {inputs : PublicBoundary} (matching : LogicalMatching mains batch inputs) :
    ((activeTokens mains batch inputs true).filterMap memoryProjection).Perm
      ((activeTokens mains batch inputs false).filterMap memoryProjection) ∧
    ((activeTokens mains batch inputs true).filterMap stateProjection).Perm
      ((activeTokens mains batch inputs false).filterMap stateProjection) :=
  NativeTokenLedgerProofs.projected_matching matching

end Airbender.NativeTokenLedger
