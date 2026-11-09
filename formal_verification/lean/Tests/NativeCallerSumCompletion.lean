import Airbender.Review.Trace.Families.ReducedMachine.CallerSumCompletionTheorems
import Airbender.Review.Helpers.Memory.DelegationSumCompletionTheorems

namespace Airbender.Tests.NativeCallerSumCompletion
open Airbender.NativeInactiveMain Airbender.NativeCallerSumCompletion
open Airbender.NativeCallerSumCompletionProofs Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
abbrev TestF := ZMod mersenne31Modulus

theorem actual_domain : callerAuxiliaryLayout.traceLength = 8388608 := by decide +kernel

theorem two_point_reserved : Verification.normalizeLast 2 (fun _ => (1 : TestF)) 1 = -1 := by decide +kernel

theorem ordinary_retains_value : Verification.normalizeLast 2 (fun _ => (7 : TestF)) 0 = 7 := by decide +kernel

theorem single_point_has_empty_ordinary : Verification.normalizeLast 1 (fun _ => (7 : TestF)) 0 = 0 := by decide +kernel

theorem wrong_reserved_rejected : Verification.normalizeLast 2 (fun _ => (1 : TestF)) 1 ≠ 1 := by decide +kernel

theorem two_point_completion : ∃ p, Delegation.SumPolynomialAccepted 2 (-1 : ℚ) p
    (Verification.normalizeLast 2 (fun _ => (1 : ℚ))) 1 := by
  simpa using Delegation.normalized_sum_polynomial (by decide : 0 < 2)
    (IsPrimitiveRoot.neg_one 0 (by decide) : IsPrimitiveRoot (-1 : ℚ) 2)
    (by norm_num : (2 : ℚ) ≠ 0) (fun _ => (1 : ℚ))

theorem single_point_completion : ∃ p, Delegation.SumPolynomialAccepted 1 (1 : ℚ) p
    (Verification.normalizeLast 1 (fun _ => (7 : ℚ))) 0 := by
  simpa using Delegation.normalized_sum_polynomial (by decide : 0 < 1)
    (IsPrimitiveRoot.one_right_iff.mpr rfl : IsPrimitiveRoot (1 : ℚ) 1)
    (by norm_num : (1 : ℚ) ≠ 0) (fun _ => (7 : ℚ))

theorem nonconstant_two_point : ∃ p, Delegation.SumPolynomialAccepted 2 (-1 : ℚ) p
    (Verification.normalizeLast 2 (fun _ => (1 : ℚ))) 1 ∧ ∀ c, p ≠ Polynomial.C c := by
  obtain ⟨p,accepted⟩ := two_point_completion
  exact ⟨p,accepted,Delegation.SumCompletionProofs.not_constant accepted (by norm_num)⟩

theorem all_ordinary_auxiliary_retained {R : Type} [Field R] (base : MainProof R) {i : Nat}
    (small : i < callerAuxiliaryLayout.traceLength-1) : normalizedAuxiliary base i = base.auxiliary i := ordinary base small

theorem all_other_columns_retained {R : Type} [Field R] (base : MainProof R) (i : Nat)
    (column : QuarticColumn) (other : column ≠ callerAuxiliaryLayout.request) :
    normalizedAuxiliary base i column = base.auxiliary i column := other_column base i column other

theorem reserved_grand_retained {R : Type} [Field R] (base : MainProof R) :
    normalizedAuxiliary base (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.grandProduct =
      base.auxiliary (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.grandProduct := grand base _

theorem reserved_decoder_retained {R : Type} [Field R] (base : MainProof R) :
    normalizedAuxiliary base (callerAuxiliaryLayout.traceLength-1) decoderAuxiliaryLayout.access =
      base.auxiliary (callerAuxiliaryLayout.traceLength-1) decoderAuxiliaryLayout.access := other_column base _ _ (by decide +kernel)

theorem exact_negative_request_sum {R : Type} [Field R] (base : MainProof R) :
    normalizedAuxiliary base (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.request =
      -requestSum base := terminal base

theorem same_original_rows {R : Type} [Field R] (base : MainProof R) :
    (normalizedMemory base).rows = base.rows := rfl

theorem original_grand_claim {R : Type} [Field R] (base : MainProof R) :
    (normalizedMemory base).grandClaim = base.grandClaim := rfl

theorem native_domain_cast {R : Type} [Field R] (embed : TestF →+* R) :
    (callerAuxiliaryLayout.traceLength : R) ≠ 0 := domain_nonzero embed

theorem old_inactive_request_kept : ∃ w, NativeInactiveMain.Fixture w := NativeInactiveMainProofs.fixture

theorem normalized_components {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    {w : Nat → TestF} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base) :
    Realizes embed memory pc ch decoder w (normalizedMemory base) := preserves embed memory pc ch decoder old

theorem genuine_caller_completion {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    {w : Nat → TestF} {base : MainProof R} (old : Realizes embed memory pc ch decoder w base)
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ completed, Completion embed memory pc ch decoder w base omega completed := complete embed memory pc ch decoder old omega primitive

theorem full_fixture : ∃ w, NativeCallerSumCompletion.Fixture w := native_inactive_caller_sum_completion
end Airbender.Tests.NativeCallerSumCompletion
