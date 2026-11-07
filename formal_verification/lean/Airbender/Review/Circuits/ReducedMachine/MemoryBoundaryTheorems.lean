import Airbender.Proofs.ReducedMachine.NativeMemoryBoundary

namespace Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native

theorem unified_worker_memory_balance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R) (config : WorkerConfiguration Setup)
    {mains : List R} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : UnifiedMemoryAccepted embed memory processor pc config mains batch inputs inverse) :
    mains.prod * registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey *
      workerBatchProduct embed memory batch true =
      registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
      workerBatchProduct embed memory batch false :=
  NativeMemoryBoundaryProofs.complete_worker_balance embed memory processor pc config accepted

end Airbender.ReducedMachine.NativeMemoryBoundary
