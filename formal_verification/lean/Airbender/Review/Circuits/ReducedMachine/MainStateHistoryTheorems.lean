import Airbender.Proofs.ReducedMachine.NativeMainStateHistory

namespace Airbender.NativeMainStateHistory
open NativeTokenLedger Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Full native logical observations derive main chronology and clock ranges;
    no execution order, per-row clock or expected intermediate state is supplied. -/
theorem native_main_state_history {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R) (pc : PCChallenges R)
    (config : WorkerConfiguration Setup) {mains : List (MainProof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed memory processor pc config mains batch inputs inverse)
    (matching : LogicalMatching mains batch inputs) : Effects mains inputs :=
  NativeMainStateHistoryProofs.history embed memory pc accepted.mainProofs matching

end Airbender.NativeMainStateHistory
