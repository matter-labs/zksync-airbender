import Airbender.Review.Circuits.Blake2Worker.DelegationTheorems

namespace Airbender.Tests.NativeBlake2Delegation
open Verification Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.Blake2Worker.AuxiliaryArtifact
set_option autoImplicit false

abbrev F := ZMod mersenne31Modulus

private noncomputable def claimProof (claim : F) : DelegationProof F :=
  ⟨fun _ _ => 0,fun _ _ => 0,0,0,0,claim⟩

theorem actual_processing_slot : auxiliaryLayout.processing.start = 1064 := by decide +kernel

theorem actual_domain : constraintsABI.traceLength = 1048576 := by decide +kernel

theorem scalar_fold_positive : statementDelegationAccumulator [3,4] [claimProof 2,claimProof 5] = 0 := by
  decide +kernel

theorem scalar_fold_bad_claim : statementDelegationAccumulator [3,4] [claimProof 2,claimProof 6] ≠ 0 := by
  decide +kernel

theorem scalar_cancellation_not_matching : statementDelegationAccumulator [3,4] [claimProof 1,claimProof 6] = 0 ∧
    ([3,4] : List F) ≠ [1,6] := by decide +kernel

theorem scalar_empty_workers : statementDelegationAccumulator ([3,-3] : List F) [] = 0 := by decide +kernel

theorem complete_worker_sum {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {proof : DelegationProof R} (accepted : DelegationAccepted embed memory processor proof) :
    workerAuxiliarySum proof = proof.delegationClaim := worker_delegation_sum embed memory processor accepted

theorem active_pole_excluded {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {proof : DelegationProof R} (accepted : DelegationAccepted embed memory processor proof)
    (i : Nat) (ordinary : i < constraintsABI.traceLength-1) :
    proof.rows i constraintsABI.multiplicity = 1 → processorArgument embed processor (proof.rows i) 1 ≠ 0 := by
  intro active
  exact (DelegationProofs.active_auxiliary embed memory processor accepted i ordinary active).1

theorem inactive_pole_not_excluded : processorAuxiliaryTerm (0 : F) 0 1 7 = 0 := by
  simp [processorAuxiliaryTerm]

theorem statement_component {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {mains : List R} {workers : List (DelegationProof R)}
    (accepted : DelegationClaimsAccepted embed memory processor mains workers) :
    mains.sum = (workers.map workerAuxiliarySum).sum := delegation_claims_balance embed memory processor accepted

end Airbender.Tests.NativeBlake2Delegation
