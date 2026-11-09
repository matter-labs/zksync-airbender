import Airbender.Review.Trace.Families.ReducedMachine.InactiveMain
import Airbender.Review.Circuits.ReducedMachine.MainArguments
import Airbender.Review.Helpers.Tables.NormalizeLast

namespace Airbender.NativeCallerSumCompletion
open Airbender.NativeInactiveMain Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native

/-- Normalize only the caller column's reserved observation. Ordinary rows and
    every other auxiliary column retain their original values. -/
noncomputable def normalizedAuxiliary {R : Type} [Field R] (base : MainProof R)
    (i : Nat) (column : QuarticColumn) : R :=
  if column = callerAuxiliaryLayout.request then
    Verification.normalizeLast callerAuxiliaryLayout.traceLength
      (fun j => base.auxiliary j callerAuxiliaryLayout.request) i
  else base.auxiliary i column

noncomputable def normalizedMemory {R : Type} [Field R] (base : MainProof R) : MainProof R :=
  ⟨base.rows,normalizedAuxiliary base,base.grandClaim⟩

def requestSum {R : Type} [Field R] (base : MainProof R) : R :=
  ∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1), base.auxiliary i callerAuxiliaryLayout.request

/-- SAME constructed main observation has the full memory component, individual
    decoder access and genuine complete caller sum polynomial. Decoder/scalar
    table families and global memory/delegation statements remain separate. -/
structure Completion {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (w : Nat → F) (base : MainProof R) (omega : R)
    (completed : Airbender.ReducedMachine.NativeMainArguments.Proof R) : Prop where
  normalized : completed.memory = normalizedMemory base
  components : Realizes embed memory pc ch decoder w completed.memory
  caller : CallerDelegationAccepted embed ch completed.caller
  domain : completed.omega = omega
  claim : completed.delegationClaim = requestSum base

/-- Existential component completion on its explicit challenge and primitive
    domain. No global source acceptance, issued-call activity or physical
    transcript is asserted. The derived claim is nonzero. -/
def Fixture (w : Nat → F) : Prop :=
  w importedConstraintsTraceColumns.execute = 0 ∧ csrRequest w = ⟨1,1991,some 0,3⟩ ∧
  ∀ {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R),
    Nonpoles embed memory pc ch w → ∀ omega, IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength →
    ∃ base completed, Completion embed memory pc ch decoder w base omega completed ∧
      completed.delegationClaim = (8388607 : R)*(csrStageThreeArgument embed ch 1 w)⁻¹ ∧
      completed.delegationClaim ≠ 0 ∧ ∀ constant, completed.polynomial ≠ Polynomial.C constant
end Airbender.NativeCallerSumCompletion
