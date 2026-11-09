import Airbender.Proofs.ReducedMachine.NativeCallerSumCompletion

namespace Airbender.NativeCallerSumCompletion
/-- An inactive request-positive native MAIN component has a genuine nonconstant
    caller sum polynomial, derived nonzero claim and normalized reserved row on
    the same full memory/decoder observation. Primitive-domain existence and
    physical FFT refinement, other table families and global source acceptance
    remain separate obligations. -/
theorem native_inactive_caller_sum_completion : ∃ w, Fixture w :=
  NativeCallerSumCompletionProofs.fixture
end Airbender.NativeCallerSumCompletion
