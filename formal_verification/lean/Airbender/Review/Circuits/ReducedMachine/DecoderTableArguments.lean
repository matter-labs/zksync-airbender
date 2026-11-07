import Airbender.Review.Circuits.ReducedMachine.DecoderTableArtifact
import Airbender.Review.Circuits.ReducedMachine.DecoderArguments
import Airbender.Review.Helpers.Memory.DelegationSum

namespace Airbender.ReducedMachine.NativeDecoderTableArguments
open Native NativeDecoderArguments NativeMemoryBoundary Airbender.Blake2Worker

/-- One main observation plus its separately typed actual physical base witness
    and setup observations and normalized decoder-difference polynomial. General
    body/physical codec, setup authentication and Rust/FFT refinement remain open. -/
structure Proof (R : Type) [Field R] where
  main : NativeMainArguments.Proof R
  witness : Nat → DecoderWitnessColumn → ZMod mersenne31Modulus
  setup : Nat → DecoderSetupColumn → ZMod mersenne31Modulus
  polynomial : Polynomial R
  omega : R

def setupColumn (slot : Fin 10) : DecoderSetupColumn := ⟨decoderTableLayout.setupStart+slot.val⟩

def setupQuery {R : Type} [Field R] (proof : Proof R) (i : Nat) : Vector (ZMod mersenne31Modulus) 10 :=
  Vector.ofFn fun slot => proof.setup i (setupColumn slot)

def queryArgument {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) (tau : R) (query : Vector (ZMod mersenne31Modulus) 10) : R :=
  (embed query[0] + ∑ i : Fin 9, ch.linear[i]*embed query[i.val+1])*tau+ch.gamma

def differenceTerm {R : Type} [Field R] (tau tableAux accessAux : R) : R := tau*(tableAux-accessAux)

def difference {R : Type} [Field R] (proof : Proof R) (i : Nat) : R :=
  proof.main.memory.auxiliary i decoderTableLayout.tableMultiplicity -
    proof.main.memory.auxiliary i decoderTableLayout.access

def auxiliarySum {R : Type} [Field R] (proof : Proof R) (tableSide : Bool) : R :=
  ∑ i ∈ Finset.range (decoderTableLayout.traceLength-1), proof.main.memory.auxiliary i
    (if tableSide then decoderTableLayout.tableMultiplicity else decoderTableLayout.access)

/-- Actual normalized difference samples/degree/domain and the native zero/last
    divisor. Neither the ordinary sum nor table membership is a premise. -/
structure DifferencePolynomialAccepted {R : Type} [Field R] (size : Nat) (omega : R)
    (polynomial : Polynomial R) (values : Nat → R) : Prop where
  positive : 0 < size
  primitive : IsPrimitiveRoot omega size
  degree : polynomial.natDegree < size
  samples : ∀ i < size, polynomial.eval (omega ^ i) = values i
  boundary : Polynomial.X*(Polynomial.X-Polynomial.C (omega ^ (size - 1))) ∣ polynomial

/-- Individual native table-multiplicity relation over ALL ordinary rows and
    the actual zero/last difference polynomial. Physical witness9 need not be
    Boolean or an issued count. No zero-outside-capacity, table equivalence,
    membership, compression-injectivity, request filter or desired sum is assumed. -/
structure TableAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : Challenges R) (proof : Proof R) : Prop where
  multiplicity : ∀ i < decoderTableLayout.traceLength-1,
    accessTerm 1 (queryArgument embed ch 1 (setupQuery proof i))
      (embed (proof.witness i decoderTableLayout.multiplicity))
      (proof.main.memory.auxiliary i decoderTableLayout.tableMultiplicity) = 0
  polynomial : DifferencePolynomialAccepted decoderTableLayout.traceLength proof.omega proof.polynomial (difference proof)

/-- Stronger same-main component, retaining all previous complete acceptances
    on the exact SAME main rows/auxiliaries and the SAME configured worker batch.
    Setup values are actual observations, not yet public-code setup fidelity. -/
structure Accepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (decoder : Challenges R)
    (config : Native.WorkerConfiguration Setup) (proofs : List (Proof R))
    (batch : Native.WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  arguments : NativeDecoderArguments.Accepted embed memory ch pc decoder config (proofs.map Proof.main) batch inputs inverse
  tables : ∀ proof ∈ proofs, TableAccepted embed decoder proof
end Airbender.ReducedMachine.NativeDecoderTableArguments
