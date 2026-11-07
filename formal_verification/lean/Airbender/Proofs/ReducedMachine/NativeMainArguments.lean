import Airbender.Review.Circuits.ReducedMachine.MainArguments
import Airbender.Proofs.ReducedMachine.NativeMainAuxiliary
import Airbender.Proofs.ReducedMachine.NativeConfiguredDelegation

namespace Airbender.ReducedMachine.NativeMainArgumentProofs
open Native NativeMainArguments NativeMainAuxiliary NativeMemoryBoundary Airbender.Blake2Worker
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem memory_acceptance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (config : Native.WorkerConfiguration Setup)
    {mains : List (Proof R)} {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : NativeMainArguments.Accepted embed memory ch pc config mains batch inputs inverse) :
    MainWorkerAccepted embed memory (workerProcessorChallenges ch) pc config (mains.map Proof.memory) batch inputs inverse := by
  refine ⟨?_,?_⟩
  · intro proof member
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact accepted.mainMemory origin present
  · simpa only [List.map_map,Function.comp_def] using accepted.globalMemory

theorem delegation_acceptance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (config : Native.WorkerConfiguration Setup)
    {mains : List (Proof R)} {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : NativeMainArguments.Accepted embed memory ch pc config mains batch inputs inverse) :
    ConfiguredCallerWorkersAccepted embed memory ch config (mains.map Proof.caller) batch := by
  refine ⟨?_,accepted.globalMemory.workers,?_⟩
  · intro proof member
    obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
    exact accepted.mainDelegation origin present
  · simpa only [List.map_map,Function.comp_def,Proof.caller] using accepted.delegationAccumulator

theorem joint_effects {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (config : Native.WorkerConfiguration Setup)
    {mains : List (Proof R)} {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : NativeMainArguments.Accepted embed memory ch pc config mains batch inputs inverse) :
    Effects embed memory pc mains batch inputs := by
  obtain ⟨scalar,capacity,multiplicity⟩ := NativeConfiguredDelegationProofs.bounded_rows_balance embed memory ch config
    (delegation_acceptance embed memory ch pc config accepted)
  refine ⟨?_,NativeMainAuxiliaryProofs.main_worker_balance embed memory (workerProcessorChallenges ch) pc config
    (memory_acceptance embed memory ch pc config accepted),capacity,multiplicity⟩
  change (mains.map fun proof => callerAuxiliarySum proof.caller).sum = _
  simpa only [List.map_map,Function.comp_def] using scalar

end Airbender.ReducedMachine.NativeMainArgumentProofs
