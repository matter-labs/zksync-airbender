import Airbender.Review.Circuits.Blake2Worker.Delegation
import Airbender.Proofs.Memory.DelegationSum
import Airbender.Proofs.Blake2Worker.NativeAuxiliary

namespace Airbender.Blake2Worker.DelegationProofs
open Verification Native AuxiliaryArtifact
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem worker_sum {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {proof : DelegationProof R} (accepted : DelegationAccepted embed memory processor proof) :
    workerAuxiliarySum proof = proof.delegationClaim :=
  Airbender.Delegation.SumProofs.ordinary_sum accepted.sumPolynomial

/-- Multiplicity-one denominator nonzeroness comes from its native auxiliary
    equation. Inactive denominators are not silently assumed nonzero. -/
theorem active_auxiliary {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {proof : DelegationProof R} (accepted : DelegationAccepted embed memory processor proof)
    (i : Nat) (ordinary : i < constraintsABI.traceLength-1) :
    proof.rows i constraintsABI.multiplicity = 1 →
      processorArgument embed processor (proof.rows i) 1 ≠ 0 ∧
      proof.auxiliary i auxiliaryLayout.processing = (processorArgument embed processor (proof.rows i) 1)⁻¹ := by
  intro active
  have equation := (AuxiliaryProofs.row_balance embed memory processor (accepted.trace.rows i ordinary)).1
  rw [active,map_one] at equation
  have nonzero : processorArgument embed processor (proof.rows i) 1 ≠ 0 := by
    intro zero
    rw [zero,zero_mul] at equation
    exact zero_ne_one equation
  refine ⟨nonzero,?_⟩
  calc
    proof.auxiliary i auxiliaryLayout.processing =
        (processorArgument embed processor (proof.rows i) 1)⁻¹ *
          (processorArgument embed processor (proof.rows i) 1 * proof.auxiliary i auxiliaryLayout.processing) := by
      rw [← mul_assoc,inv_mul_cancel₀ nonzero,one_mul]
    _ = _ := by rw [equation,mul_one]

/-- Pure reference for the actual source fold; no caller/worker matching premise. -/
theorem subtract_fold {R : Type} [Field R] (claims : List R) (initial : R) :
    claims.foldl (·-·) initial = initial-claims.sum := by
  induction claims generalizing initial with
  | nil => simp
  | cons claim claims ih =>
      simp only [List.foldl_cons,List.sum_cons,ih]
      ring

theorem worker_fold {R : Type} [Field R] (proofs : List (DelegationProof R)) (initial : R) :
    proofs.foldl (fun accumulator proof => accumulator-proof.delegationClaim) initial =
      (proofs.map DelegationProof.delegationClaim).foldl (·-·) initial := by
  induction proofs generalizing initial with
  | nil => rfl
  | cons proof proofs ih => simpa only [List.foldl_cons,List.map_cons] using ih (initial-proof.delegationClaim)

theorem add_fold {R : Type} [Field R] (claims : List R) (initial : R) :
    claims.foldl (·+·) initial = initial+claims.sum := by
  induction claims generalizing initial with
  | nil => simp
  | cons claim claims ih =>
      simp only [List.foldl_cons,List.sum_cons,ih]
      ring

theorem accumulator_normal_form {R : Type} [Field R] (mains : List R) (proofs : List (DelegationProof R)) :
    statementDelegationAccumulator mains proofs = mains.sum-(proofs.map DelegationProof.delegationClaim).sum := by
  unfold statementDelegationAccumulator
  rw [worker_fold,subtract_fold,add_fold,zero_add]

theorem claims_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {mains : List R} {proofs : List (DelegationProof R)}
    (accepted : DelegationClaimsAccepted embed memory processor mains proofs) :
    mains.sum = (proofs.map workerAuxiliarySum).sum := by
  have claim := accepted.accumulator
  rw [accumulator_normal_form,sub_eq_zero] at claim
  have same : proofs.map DelegationProof.delegationClaim = proofs.map workerAuxiliarySum := by
    apply List.map_congr_left
    intro proof member
    exact (worker_sum embed memory processor (accepted.proofs proof member)).symm
  rw [same] at claim
  exact claim

end Airbender.Blake2Worker.DelegationProofs
