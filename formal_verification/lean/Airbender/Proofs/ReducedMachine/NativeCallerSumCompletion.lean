import Airbender.Proofs.ReducedMachine.NativeInactiveMain
import Airbender.Proofs.Memory.DelegationSumCompletion
import Airbender.Review.Trace.Families.ReducedMachine.CallerSumCompletion

namespace Airbender.NativeCallerSumCompletionProofs
open Airbender.NativeInactiveMain Airbender.NativeCallerSumCompletion
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem ordinary {R : Type} [Field R] (base : MainProof R) {i : Nat}
    (small : i < callerAuxiliaryLayout.traceLength-1) :
    normalizedAuxiliary base i = base.auxiliary i := by
  classical
  funext column
  simp only [normalizedAuxiliary]
  split
  · rename_i same
    subst column
    exact Verification.NormalizeLastProofs.ordinary _ small
  · rfl

theorem other_column {R : Type} [Field R] (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (other : column ≠ callerAuxiliaryLayout.request) :
    normalizedAuxiliary base i column = base.auxiliary i column := by
  simp only [normalizedAuxiliary,if_neg other]

theorem request_column {R : Type} [Field R] (base : MainProof R) (i : Nat) :
    normalizedAuxiliary base i callerAuxiliaryLayout.request =
      Verification.normalizeLast callerAuxiliaryLayout.traceLength
        (fun j => base.auxiliary j callerAuxiliaryLayout.request) i := by
  simp [normalizedAuxiliary]

theorem terminal {R : Type} [Field R] (base : MainProof R) :
    normalizedAuxiliary base (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.request =
      -requestSum base := by
  rw [request_column]
  exact Verification.NormalizeLastProofs.terminal _ _

theorem grand {R : Type} [Field R] (base : MainProof R) (i : Nat) :
    normalizedAuxiliary base i callerAuxiliaryLayout.grandProduct =
      base.auxiliary i callerAuxiliaryLayout.grandProduct :=
  other_column base i _ (by decide +kernel)

theorem preserves {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    {w : Nat → F} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base) :
    Realizes embed memory pc ch decoder w (normalizedMemory base) := by
  refine ⟨old.1,old.2.1,⟨?_,?_,?_⟩,?_,?_⟩
  · intro i small
    change RowAccepted embed memory pc (base.rows i) (normalizedAuxiliary base i)
      (normalizedAuxiliary base (i+1) callerAuxiliaryLayout.grandProduct)
    rw [ordinary base small,grand]
    exact old.2.2.1.rows i small
  · change grandBoundaryTerm 1 (normalizedAuxiliary base 0 callerAuxiliaryLayout.grandProduct) 1 = 0
    rw [grand]
    exact old.2.2.1.first
  · change grandBoundaryTerm 1
      (normalizedAuxiliary base (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.grandProduct) base.grandClaim = 0
    rw [grand]
    exact old.2.2.1.last
  · intro i small
    change callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (base.rows i))
      (embed (csrRequest (base.rows i)).multiplicity) (normalizedAuxiliary base i callerAuxiliaryLayout.request) = 0
    rw [ordinary base small]
    exact old.2.2.2.1 i small
  · intro i small
    change Airbender.ReducedMachine.NativeDecoderArguments.RowAccepted embed decoder
      (base.rows i) (normalizedAuxiliary base i)
    rw [ordinary base small]
    exact old.2.2.2.2 i small

theorem domain_nonzero {R : Type} [Field R] (embed : F →+* R) :
    (callerAuxiliaryLayout.traceLength : R) ≠ 0 := by
  change (8388608 : R) ≠ 0
  have scalar : (8388608 : F) ≠ 0 := by decide +kernel
  intro zero
  apply scalar
  apply embed.injective
  have cast : embed (8388608 : F) = (8388608 : R) := by
    simpa only [Nat.cast_ofNat] using map_natCast embed 8388608
  simpa only [map_zero] using cast.trans zero

theorem complete {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    {w : Nat → F} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base)
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ completed, Completion embed memory pc ch decoder w base omega completed := by
  obtain ⟨polynomial,accepted⟩ := Airbender.Delegation.SumCompletionProofs.normalized_completion
    (by decide : 0 < callerAuxiliaryLayout.traceLength) primitive (domain_nonzero embed)
    (fun j => base.auxiliary j callerAuxiliaryLayout.request)
  let completed : NativeMainArguments.Proof R := ⟨normalizedMemory base,polynomial,omega,requestSum base⟩
  have components := preserves embed memory pc ch decoder old
  have caller : CallerDelegationAccepted embed ch
      ⟨base.rows,normalizedAuxiliary base,polynomial,omega,requestSum base⟩ := by
    refine ⟨?_,components.2.2.2.1,?_⟩
    · intro i small
      exact (components.2.2.1.rows i small).body
    · simpa only [request_column,requestSum] using accepted
  have view : completed.caller =
      ⟨base.rows,normalizedAuxiliary base,polynomial,omega,requestSum base⟩ := by
    simp only [completed,NativeMainArguments.Proof.caller,normalizedMemory]
  refine ⟨completed,?_⟩
  exact { normalized := rfl
          components := components
          caller := by rw [view]; exact caller
          domain := rfl
          claim := by simp only [completed] }

theorem fixture : ∃ w, NativeCallerSumCompletion.Fixture w := by
  let w := NativeCSRPositiveWitness.assignment false
  refine ⟨w,(NativeCSRBodyPaddingProofs.observations false).1,
    (NativeCSRBodyPaddingProofs.observations false).2,?_⟩
  intro R _ embed memory pc ch decoder nonpoles omega primitive
  let base := NativeInactiveMainProofs.proof embed memory pc ch w
  have old : Realizes embed memory pc ch decoder w base :=
    NativeInactiveMainProofs.realizes embed memory pc ch decoder (NativeCSRPositiveWitness.body false)
      (by rfl) (by
        intro column member
        rw [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)
      (congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2) nonpoles
  obtain ⟨completed,accepted⟩ := complete embed memory pc ch decoder old omega primitive
  have nonzero : completed.delegationClaim ≠ 0 := by
    rw [accepted.claim]
    exact NativeInactiveMainProofs.request_sum_nonzero embed memory pc ch w nonpoles
  refine ⟨base,completed,accepted,?_,nonzero,?_⟩
  · rw [accepted.claim]
    exact NativeInactiveMainProofs.request_sum embed memory pc ch w
  · exact Airbender.Delegation.SumCompletionProofs.not_constant accepted.caller.sumPolynomial nonzero
end Airbender.NativeCallerSumCompletionProofs
