import Airbender.Review.Circuits.ReducedMachine.Delegation
import Airbender.Proofs.ReducedMachine.NativeCSRArgument
import Airbender.Proofs.Memory.DelegationSum
import Airbender.Proofs.Blake2Worker.NativeDelegation

namespace Airbender.ReducedMachine.NativeCallerDelegationProofs
open Native Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem same_source : callerAuxiliaryLayoutSourceBytes = importedConstraintsSourceBytes := rfl

theorem geometry : callerAuxiliaryLayout.traceLength = importedConstraintsSetupColumns.traceLength ∧
    callerAuxiliaryLayout.traceLength = 8388608 ∧ callerAuxiliaryLayout.extensionOffset = 12 ∧
    callerAuxiliaryLayout.width = 124 ∧ callerAuxiliaryLayout.request.start = 92 ∧
    callerAuxiliaryLayout.memory.size = 3 ∧ callerAuxiliaryLayout.state.start = 108 ∧
    callerAuxiliaryLayout.masking.start = 112 ∧ callerAuxiliaryLayout.initialization.start = 116 ∧
    callerAuxiliaryLayout.grandProduct.start = 120 := by decide +kernel

theorem memory_columns (slot : Fin 3) : (callerAuxiliaryLayout.memory[slot.val]!).start = 96+4*slot.val := by
  fin_cases slot <;> decide +kernel

theorem caller_sum {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) {proof : CallerDelegationProof R}
    (accepted : CallerDelegationAccepted embed ch proof) : callerAuxiliarySum proof = proof.delegationClaim :=
  Airbender.Delegation.SumProofs.ordinary_sum accepted.sumPolynomial

/-- Exact precompression caller observables; all ordinary rows are retained,
    including multiplicity0. No issued or selected stream is supplied. -/
theorem row_equation {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) {proof : CallerDelegationProof R}
    (accepted : CallerDelegationAccepted embed ch proof) (i : Nat)
    (ordinary : i < callerAuxiliaryLayout.traceLength-1) :
    csrArgument ch (csrCallerKey embed (csrCallerObservation (.mk .reduced (proof.rows i)))) *
      proof.auxiliary i callerAuxiliaryLayout.request = embed (csrRequest (proof.rows i)).multiplicity := by
  have equation := accepted.auxiliary i ordinary
  simp only [callerAuxiliaryTerm,one_mul,sub_eq_zero] at equation
  rw [NativeCSRArgumentProofs.unit_scaling,NativeCSRArgumentProofs.stage_two] at equation
  exact equation

theorem active_auxiliary {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) {proof : CallerDelegationProof R}
    (accepted : CallerDelegationAccepted embed ch proof) (i : Nat)
    (ordinary : i < callerAuxiliaryLayout.traceLength-1) :
    (csrRequest (proof.rows i)).multiplicity = 1 →
    csrArgument ch (csrCallerKey embed (csrCallerObservation (.mk .reduced (proof.rows i)))) ≠ 0 := by
  intro active zero
  have equation := row_equation embed ch accepted i ordinary
  rw [active,map_one,zero,zero_mul] at equation
  exact zero_ne_one equation

theorem rows_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    {callers : List (CallerDelegationProof R)} {workers : List (Airbender.Blake2Worker.Native.DelegationProof R)}
    (accepted : CallerWorkerClaimsAccepted embed memory ch callers workers) :
    (callers.map callerAuxiliarySum).sum = (workers.map Airbender.Blake2Worker.Native.workerAuxiliarySum).sum := by
  have balance := Airbender.Blake2Worker.DelegationProofs.claims_balance embed memory (workerProcessorChallenges ch) accepted.component
  have same : callers.map CallerDelegationProof.delegationClaim = callers.map callerAuxiliarySum := by
    apply List.map_congr_left
    intro proof member
    exact (caller_sum embed ch (accepted.callerProofs proof member)).symm
  rw [same] at balance
  exact balance

end Airbender.ReducedMachine.NativeCallerDelegationProofs
