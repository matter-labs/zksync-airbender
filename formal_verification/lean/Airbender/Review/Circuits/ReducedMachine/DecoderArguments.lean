import Airbender.Review.Circuits.ReducedMachine.DecoderAuxiliaryArtifact
import Airbender.Review.Circuits.ReducedMachine.Decoder
import Airbender.Review.Circuits.ReducedMachine.MainArguments

namespace Airbender.ReducedMachine.NativeDecoderArguments
open Native Airbender.Blake2Worker NativeMemoryBoundary

/-- Actual nine decoder linearization challenges and additive challenge.
    The low PC field has literal coefficient one in the native source. -/
structure Challenges (R : Type) where
  linear : Vector R 9
  gamma : R

def argument {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) (tau : R) (w : Nat → ZMod mersenne31Modulus) : R :=
  (embed (decoderQuery w)[0] + ∑ i : Fin 9, ch.linear[i] * embed (decoderQuery w)[i.val+1]) * tau + ch.gamma

/-- Source scaling: execute is subtracted without an inner tau factor. -/
def accessTerm {R : Type} [Field R] (tau denominator execute accumulator : R) : R :=
  tau * (denominator*accumulator-execute)

/-- Complete actual native body and individual unit-normalized decoder-access
    relation. Table multiplicities, sum/last-row consistency, extraction and
    physical Rust/field/LDE/quotient enforcement remain separate. This interface
    supplies no table membership, expected query, request filter or active flag. -/
structure RowAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) (w : Nat → ZMod mersenne31Modulus) (aux : QuarticColumn → R) : Prop where
  body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table)
  access : accessTerm 1 (argument embed ch 1 w) (embed (w importedConstraintsTraceColumns.execute))
    (aux decoderAuxiliaryLayout.access) = 0

/-- Extend the same-main argument interface on its exact same rows/auxiliaries.
    All ordinary rows remain, including inactive decoder accesses and callers. -/
structure Accepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (decoder : Challenges R)
    (config : Native.WorkerConfiguration Setup) (mains : List (NativeMainArguments.Proof R))
    (batch : Native.WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  arguments : NativeMainArguments.Accepted embed memory ch pc config mains batch inputs inverse
  decoderAccess : ∀ proof ∈ mains, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    RowAccepted embed decoder (proof.memory.rows i) (proof.memory.auxiliary i)

end Airbender.ReducedMachine.NativeDecoderArguments
