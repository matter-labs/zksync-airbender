import Airbender.Review.Circuits.ReducedMachine.MainArgumentTheorems

namespace Airbender.Tests.NativeMainArguments
open Airbender.ReducedMachine Airbender.ReducedMachine.NativeMainArguments
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem shared_body {R : Type} [Field R] (proof : Proof R) : proof.caller.rows = proof.memory.rows := rfl

theorem shared_auxiliary {R : Type} [Field R] (proof : Proof R) : proof.caller.auxiliary = proof.memory.auxiliary := rfl

theorem shared_claim {R : Type} [Field R] (proof : Proof R) : proof.caller.delegationClaim = proof.delegationClaim := rfl

theorem full_domain : Native.callerAuxiliaryLayout.traceLength = 8388608 := by decide +kernel

/-- Distinct observed claims are retained. This is observation data only,
    not an accepted main/worker witness or a scalar/product enforcement test. -/
noncomputable def distinctClaims : Proof (ZMod mersenne31Modulus) :=
  ⟨⟨fun _ _ => 0,fun _ _ => 0,1⟩,0,0,0⟩

theorem claims_not_identified : distinctClaims.memory.grandClaim = 1 ∧ distinctClaims.caller.delegationClaim = 0 :=
  ⟨rfl,rfl⟩

theorem same_main_auxiliary_sum {R : Type} [Field R] (proof : Proof R) :
    mainCallerSum proof = ∑ i ∈ Finset.range (Native.callerAuxiliaryLayout.traceLength-1),
      proof.memory.auxiliary i Native.callerAuxiliaryLayout.request := rfl

theorem complete_joint_components {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : Airbender.ReducedMachine.Native.CSRArgumentChallenges R) (pc : PCChallenges R) (config : Native.WorkerConfiguration Setup)
    {mains : List (Proof R)} {batch : Native.WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc config mains batch inputs inverse) : Effects embed memory pc mains batch inputs :=
  same_main_arguments embed memory ch pc config accepted

end Airbender.Tests.NativeMainArguments
