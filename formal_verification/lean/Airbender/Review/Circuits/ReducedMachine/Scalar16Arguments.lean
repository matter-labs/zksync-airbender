import Airbender.Review.Circuits.ReducedMachine.Scalar16Artifact
import Airbender.Review.Circuits.ReducedMachine.InitializationRange
import Airbender.Review.Circuits.ReducedMachine.DecoderTableArguments

namespace Airbender.NativeScalar16Arguments
open Airbender.ReducedMachine.Native
abbrev F := ZMod mersenne31Modulus

def bodyProduct (slot : Fin 4) : BaseAuxiliaryColumn := ⟨scalar16Layout.bodyProductStart.index+slot.val⟩
def bodyAccumulator (slot : Fin 4) : Airbender.Blake2Worker.QuarticColumn :=
  ⟨scalar16Layout.bodyAccumulatorStart.start+4*slot.val⟩

def bodyPair (w : Nat → F) (slot : Fin 4) : Vector F 2 :=
  #v[w (scalar16Layout.bodyColumns[2 * slot.val]'(by omega)),
    w (scalar16Layout.bodyColumns[2 * slot.val + 1]'(by omega))]

def tableTerm {R : Type} [CommRing R] (tau gamma value multiplicity accumulator : R) : R :=
  tau*((gamma+tau*value)*accumulator-multiplicity)

def differenceTerm {R : Type} [CommRing R] (tau table : R) (body : Fin 4 → R) (initialization : R) : R :=
  tau*(table-((∑ slot : Fin 4,body slot) + initialization))

/-- SAME existing initialization main/base observations, separately typed
    actual physical table observations and actual normalized difference polynomial.
    This supplies no public table authentication or physical codec refinement. -/
structure Proof (R : Type) [Field R] where
  initialization : Airbender.NativeInitializationRange.Proof R
  witness : Nat → Scalar16WitnessColumn → F
  setup : Nat → Scalar16SetupColumn → F
  polynomial : Polynomial R
  omega : R

def pairSum {R : Type} [Field R] (proof : Proof R) (i : Nat) : R :=
  (∑ slot : Fin 4,proof.initialization.main.auxiliary i (bodyAccumulator slot))+
    proof.initialization.main.auxiliary i scalar16Layout.initializationAccumulator

def difference {R : Type} [Field R] (proof : Proof R) (i : Nat) : R :=
  proof.initialization.main.auxiliary i scalar16Layout.tableAccumulator-pairSum proof i

def auxiliarySum {R : Type} [Field R] (proof : Proof R) (tableSide : Bool) : R :=
  ∑ i ∈ Finset.range (scalar16Layout.traceLength-1),
    if tableSide then proof.initialization.main.auxiliary i scalar16Layout.tableAccumulator else pairSum proof i

/-- The four original native variable pairs. The extra initialization pair
    remains checked by the unchanged parent acceptance on the SAME main proof. -/
structure BodyPairAccepted {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    (w : Nat → F) (base : BaseAuxiliaryColumn → F)
    (aux : Airbender.Blake2Worker.QuarticColumn → R) (slot : Fin 4) : Prop where
  product : Airbender.NativeInitializationRange.productTerm (1 : F) (bodyPair w slot)[0]
    (bodyPair w slot)[1] (base (bodyProduct slot)) = 0
  rational : Airbender.NativeInitializationRange.rationalTerm 1 gamma
    (embed (bodyPair w slot)[0]) (embed (bodyPair w slot)[1])
    (embed (base (bodyProduct slot))) (aux (bodyAccumulator slot)) = 0

/-- All ordinary source relations and genuine zero/last difference-polynomial
    divisibility on the SAME complete main/init/ordering proof. No sum, table
    membership, address range, expected query/value/stream, multiplicity bit/count,
    zero-outside-capacity, inverse or nonzero factor is a premise. This is not
    a cryptographic or physical field/LDE/quotient extraction theorem. -/
structure Accepted {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R)
    (gamma : R) (proof : Proof R) : Prop where
  initialization : Airbender.NativeInitializationRange.Accepted embed memory pc gamma proof.initialization
  bodyPairs : ∀ i < scalar16Layout.traceLength-1, ∀ slot : Fin 4,
    BodyPairAccepted embed gamma (proof.initialization.main.rows i) (proof.initialization.base i)
      (proof.initialization.main.auxiliary i) slot
  table : ∀ i < scalar16Layout.traceLength-1,
    tableTerm 1 gamma (embed (proof.setup i scalar16Layout.setup))
      (embed (proof.witness i scalar16Layout.multiplicity))
      (proof.initialization.main.auxiliary i scalar16Layout.tableAccumulator) = 0
  consistency : Airbender.ReducedMachine.NativeDecoderTableArguments.DifferencePolynomialAccepted
    scalar16Layout.traceLength proof.omega proof.polynomial (difference proof)
end Airbender.NativeScalar16Arguments
