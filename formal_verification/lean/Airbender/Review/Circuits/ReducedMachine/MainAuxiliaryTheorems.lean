import Airbender.Proofs.ReducedMachine.NativeMainAuxiliary

namespace Airbender.ReducedMachine.NativeMainAuxiliary
open NativeMemoryBoundary Airbender.Blake2Worker.Native

theorem main_auxiliary_product {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : Accepted embed memory pc proof) :
    proof.grandClaim*mainRowsProduct embed memory pc proof false = mainRowsProduct embed memory pc proof true :=
  NativeMainAuxiliaryProofs.trace_balance embed memory pc accepted

theorem unified_main_worker_memory_balance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R) (config : WorkerConfiguration Setup)
    {mains : List (MainProof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed memory processor pc config mains batch inputs inverse) :
    registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey *
      mainBatchProduct embed memory pc mains true * workerBatchProduct embed memory batch true =
      registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
      mainBatchProduct embed memory pc mains false * workerBatchProduct embed memory batch false :=
  NativeMainAuxiliaryProofs.main_worker_balance embed memory processor pc config accepted

end Airbender.ReducedMachine.NativeMainAuxiliary
