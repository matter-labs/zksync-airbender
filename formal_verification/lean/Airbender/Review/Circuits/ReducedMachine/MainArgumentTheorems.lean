import Airbender.Proofs.ReducedMachine.NativeMainArguments

namespace Airbender.ReducedMachine.NativeMainArguments
open Native NativeMemoryBoundary Airbender.Blake2Worker

theorem same_main_arguments {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (config : Native.WorkerConfiguration Setup)
    {mains : List (Proof R)} {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc config mains batch inputs inverse) :
    Effects embed memory pc mains batch inputs :=
  NativeMainArgumentProofs.joint_effects embed memory ch pc config accepted

end Airbender.ReducedMachine.NativeMainArguments
