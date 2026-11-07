import Airbender.Proofs.ReducedMachine.NativeScalar16Arguments

namespace Airbender.NativeScalar16Arguments
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native

/-- Native zero/last consistency derives equality of ALL ordinary table
    auxiliaries with ALL five pair auxiliaries. This is not lookup extraction. -/
theorem native_scalar16_auxiliary_sum {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    auxiliarySum proof true = auxiliarySum proof false :=
  NativeScalar16ArgumentProofs.auxiliary_sum embed memory pc gamma accepted

/-- Reserved-last consistency equates the table auxiliary to the sum of the
    four body-pair auxiliaries AND the initialization pair; none is assumed zero. -/
theorem native_scalar16_last {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    proof.initialization.main.auxiliary (scalar16Layout.traceLength-1) scalar16Layout.tableAccumulator =
      pairSum proof (scalar16Layout.traceLength-1) :=
  NativeScalar16ArgumentProofs.last_auxiliaries embed memory pc gamma accepted
end Airbender.NativeScalar16Arguments
