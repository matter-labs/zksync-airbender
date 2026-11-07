import Airbender.Review.Circuits.ReducedMachine.InitializationRangeArtifact
import Airbender.Review.Circuits.ReducedMachine.InitializationOrdering

namespace Airbender.NativeInitializationRange
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
abbrev F := ZMod mersenne31Modulus

/-- Native base-field oracle relation, with BOTH half-domain scalings. -/
def productTerm {R : Type} [CommRing R] (tau a b c : R) : R := tau*(tau*a*b-c)

/-- Native rational pair relation. The accumulator and product oracle each
    receive a half-domain scaling; the numerator has literal two gamma. -/
def rationalTerm {R : Type} [CommRing R] (tau gamma a b c accumulator : R) : R :=
  (gamma^2+gamma*tau*(a+b)+tau*c)*(accumulator*tau)-(tau*(a+b)+2*gamma)

/-- Individual normalized source equations on ACTUAL address126/127, BASE4
    and QUARTIC28. These are not body4/28. This relation supplies no range,
    lookup membership, inverse/nonzero, challenge-generic identity or desired
    address comparison. Physical field/LDE/quotient extraction stays separate. -/
structure PairAccepted {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    (w : Nat → F) (base : BaseAuxiliaryColumn → F)
    (aux : Airbender.Blake2Worker.QuarticColumn → R) : Prop where
  product : productTerm (1 : F) (Airbender.NativeInitializationOrdering.address w)[0]
    (Airbender.NativeInitializationOrdering.address w)[1] (base initializationRangeLayout.product) = 0
  rational : rationalTerm 1 gamma (embed (Airbender.NativeInitializationOrdering.address w)[0])
    (embed (Airbender.NativeInitializationOrdering.address w)[1])
    (embed (base initializationRangeLayout.product)) (aux initializationRangeLayout.accumulator) = 0

/-- One SAME existing complete main proof and separately typed base-field
    stage2 observations. All original body/auxiliary/padding/grand boundaries
    and every actual adjacent-ordering relation remain on this main proof. -/
structure Proof (R : Type) [Field R] where
  main : MainProof R
  base : Nat → BaseAuxiliaryColumn → F

structure Accepted {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R)
    (gamma : R) (proof : Proof R) : Prop where
  ordering : Airbender.NativeInitializationOrdering.Accepted embed memory pc proof.main
  pairs : ∀ i < initializationRangeLayout.traceLength-1,
    PairAccepted embed gamma (proof.main.rows i) (proof.base i) (proof.main.auxiliary i)
end Airbender.NativeInitializationRange
