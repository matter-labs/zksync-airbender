import Airbender.Review.Circuits.ReducedMachine.Scalar16Arguments
import Airbender.Proofs.ReducedMachine.NativeInitializationRange
import Airbender.Proofs.ReducedMachine.NativeDecoderTableArguments

namespace Airbender.NativeScalar16ArgumentProofs
open Airbender.NativeScalar16Arguments Airbender.ReducedMachine.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem same_source : scalar16LayoutSourceBytes = importedConstraintsSourceBytes ∧
    scalar16LayoutSourceBytes = initializationRangeLayoutSourceBytes := ⟨rfl,rfl⟩

theorem geometry : scalar16Layout.traceLength = 8388608 ∧ scalar16Layout.witnessWidth = 107 ∧
    scalar16Layout.setupWidth = 16 ∧ scalar16Layout.extensionOffset = 12 ∧ scalar16Layout.width = 124 ∧
    scalar16Layout.bodyColumns = #v[61,62,69,70,90,91,122,123] ∧
    scalar16Layout.bodyProductStart.index = 0 ∧ scalar16Layout.bodyAccumulatorStart.start = 12 ∧
    scalar16Layout.initializationProduct = initializationRangeLayout.product ∧
    scalar16Layout.initializationAccumulator = initializationRangeLayout.accumulator ∧
    scalar16Layout.multiplicity.index = 7 ∧ scalar16Layout.setup.index = 0 ∧
    scalar16Layout.tableAccumulator.start = 76 ∧ scalar16Layout.traceLength = initializationRangeLayout.traceLength := by decide +kernel

/-- Literal sequential source subtraction, including the extra initialization
    pair, agrees with the finite-sum view before any native-domain instantiation. -/
theorem difference_source {R : Type} [CommRing R] (tau table : R) (body : Fin 4 → R) (initialization : R) :
    differenceTerm tau table body initialization =
      tau*(table-body 0-body 1-body 2-body 3 - initialization) := by
  simp only [differenceTerm,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change tau*(table-((body 0+(body 1+(body 2+(body 3+0)))) + initialization)) = _
  ring

theorem table_row {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    (gamma+embed (proof.setup i scalar16Layout.setup))*
      proof.initialization.main.auxiliary i scalar16Layout.tableAccumulator =
      embed (proof.witness i scalar16Layout.multiplicity) := by
  simpa only [tableTerm,one_mul,sub_eq_zero] using accepted.table i ordinary

theorem table_nonpole {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1)
    (nonzero : proof.witness i scalar16Layout.multiplicity ≠ 0) :
    gamma+embed (proof.setup i scalar16Layout.setup) ≠ 0 := by
  intro pole
  have h := table_row embed memory pc gamma accepted i ordinary
  rw [pole,zero_mul] at h
  exact nonzero (embed.injective (by simpa only [map_zero] using h.symm))

theorem body_pair_product {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} {slot : Fin 4}
    (accepted : BodyPairAccepted embed gamma w base aux slot) :
    base (bodyProduct slot) = (bodyPair w slot)[0]*(bodyPair w slot)[1] := by
  have h : (bodyPair w slot)[0]*(bodyPair w slot)[1]-base (bodyProduct slot) = 0 := by
    simpa only [Airbender.NativeInitializationRange.productTerm,one_mul] using accepted.product
  exact (sub_eq_zero.mp h).symm

theorem body_pair_factored {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} {slot : Fin 4}
    (accepted : BodyPairAccepted embed gamma w base aux slot) :
    (gamma+embed (bodyPair w slot)[0])*(gamma+embed (bodyPair w slot)[1])*
      aux (bodyAccumulator slot) = (gamma+embed (bodyPair w slot)[0])+(gamma+embed (bodyPair w slot)[1]) := by
  have product := body_pair_product embed gamma accepted
  have h := accepted.rational
  rw [product,map_mul] at h
  dsimp only [Airbender.NativeInitializationRange.rationalTerm] at h
  linear_combination h

theorem auxiliary_sum {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    auxiliarySum proof true = auxiliarySum proof false := by
  have h := Airbender.Delegation.SumProofs.ordinary_sum
    (Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.as_sum accepted.consistency)
  simp only [difference,Finset.sum_sub_distrib] at h
  exact sub_eq_zero.mp h

theorem polynomial_zero {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) : proof.polynomial.eval 0 = 0 :=
  (Airbender.Delegation.SumProofs.boundary_values
    (Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.as_sum accepted.consistency)).1

theorem last_auxiliaries {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    proof.initialization.main.auxiliary (scalar16Layout.traceLength-1) scalar16Layout.tableAccumulator =
      pairSum proof (scalar16Layout.traceLength-1) := by
  have h := (Airbender.Delegation.SumProofs.boundary_values
    (Airbender.ReducedMachine.NativeDecoderTableArgumentProofs.as_sum accepted.consistency)).2
  rw [accepted.consistency.samples _ (Nat.sub_lt accepted.consistency.positive (by decide))] at h
  exact sub_eq_zero.mp (by simpa only [difference,neg_zero] using h)
end Airbender.NativeScalar16ArgumentProofs
