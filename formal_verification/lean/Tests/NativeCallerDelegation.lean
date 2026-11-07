import Airbender.Review.Circuits.ReducedMachine.DelegationTheorems

namespace Airbender.Tests.NativeCallerDelegation
open Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeCallerDelegationProofs
set_option autoImplicit false

abbrev F := ZMod mersenne31Modulus

theorem full_source : callerAuxiliaryLayoutSourceBytes = importedConstraintsSourceBytes := same_source

theorem exact_geometry : callerAuxiliaryLayout.traceLength = 8388608 ∧
    callerAuxiliaryLayout.extensionOffset = 12 ∧ callerAuxiliaryLayout.width = 124 ∧
    callerAuxiliaryLayout.request.start = 92 := by decide +kernel

theorem all_memory_slots (slot : Fin 3) : (callerAuxiliaryLayout.memory[slot.val]!).start = 96+4*slot.val :=
  memory_columns slot

theorem other_families_retained : callerAuxiliaryLayout.state.start = 108 ∧
    callerAuxiliaryLayout.masking.start = 112 ∧ callerAuxiliaryLayout.initialization.start = 116 ∧
    callerAuxiliaryLayout.grandProduct.start = 120 := by decide +kernel

theorem separate_body_and_auxiliary_roles :
    (csrRequest (fun i => if i = 92 then (1 : F) else 0)).multiplicity = 1 ∧
    callerAuxiliaryTerm (1 : F) 1 1 7 ≠ 0 := by decide +kernel

theorem bad_active_auxiliary : callerAuxiliaryTerm (1 : F) 1 1 0 ≠ 0 := by decide +kernel

theorem inactive_pole_not_excluded : callerAuxiliaryTerm (1 : F) 0 0 7 = 0 := by
  simp [callerAuxiliaryTerm]

theorem shared_challenge_roles {R : Type} [Field R] (ch : CSRArgumentChallenges R) :
    (workerProcessorChallenges ch).gamma = ch.gamma ∧
    (workerProcessorChallenges ch).abiHigh = ch.abi ∧
    (workerProcessorChallenges ch).timeLow = ch.low ∧
    (workerProcessorChallenges ch).timeHigh = ch.high := ⟨rfl,rfl,rfl,rfl⟩

theorem complete_caller_sum {R : Type} [Field R] (embed : F →+* R) (ch : CSRArgumentChallenges R)
    {proof : CallerDelegationProof R} (accepted : CallerDelegationAccepted embed ch proof) :
    callerAuxiliarySum proof = proof.delegationClaim := caller_delegation_sum embed ch accepted

theorem actual_observation_equation {R : Type} [Field R] (embed : F →+* R) (ch : CSRArgumentChallenges R)
    {proof : CallerDelegationProof R} (accepted : CallerDelegationAccepted embed ch proof)
    (i : Nat) (ordinary : i < callerAuxiliaryLayout.traceLength-1) :
    csrArgument ch (csrCallerKey embed (csrCallerObservation (.mk .reduced (proof.rows i)))) *
      proof.auxiliary i callerAuxiliaryLayout.request = embed (csrRequest (proof.rows i)).multiplicity :=
  row_equation embed ch accepted i ordinary

theorem active_pole_excluded {R : Type} [Field R] (embed : F →+* R) (ch : CSRArgumentChallenges R)
    {proof : CallerDelegationProof R} (accepted : CallerDelegationAccepted embed ch proof)
    (i : Nat) (ordinary : i < callerAuxiliaryLayout.traceLength-1) :
    (csrRequest (proof.rows i)).multiplicity = 1 →
    csrArgument ch (csrCallerKey embed (csrCallerObservation (.mk .reduced (proof.rows i)))) ≠ 0 :=
  active_auxiliary embed ch accepted i ordinary

theorem complete_rows_balance {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    {callers : List (CallerDelegationProof R)} {workers : List (Airbender.Blake2Worker.Native.DelegationProof R)}
    (accepted : CallerWorkerClaimsAccepted embed memory ch callers workers) :
    (callers.map callerAuxiliarySum).sum = (workers.map Airbender.Blake2Worker.Native.workerAuxiliarySum).sum :=
  caller_worker_rows_balance embed memory ch accepted

end Airbender.Tests.NativeCallerDelegation
