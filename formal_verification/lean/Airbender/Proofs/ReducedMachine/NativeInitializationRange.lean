import Airbender.Review.Circuits.ReducedMachine.InitializationRange
import Airbender.Proofs.ReducedMachine.NativeInitializationOrdering

namespace Airbender.NativeInitializationRangeProofs
open Airbender.ReducedMachine.Native Airbender.NativeInitializationRange
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem same_source : initializationRangeLayoutSourceBytes = importedConstraintsSourceBytes ∧
    initializationRangeLayoutSourceBytes = callerAuxiliaryLayoutSourceBytes := ⟨rfl,rfl⟩

theorem geometry : initializationRangeLayout.traceLength = 8388608 ∧
    initializationRangeLayout.traceLength = callerAuxiliaryLayout.traceLength ∧
    initializationRangeLayout.extensionOffset = 12 ∧ initializationRangeLayout.width = 124 ∧
    initializationRangeLayout.product.index = 4 ∧ initializationRangeLayout.accumulator.start = 28 ∧
    importedConstraintsArgumentColumns.initialAddress = #v[126,127] := by decide +kernel

/-- Source scaling is preserved before specializing the logical interface to
    unit normalization. This is algebra, not a claim that physical tau is one. -/
theorem scaled_factorization {R : Type} [CommRing R] (tau gamma a b accumulator : R) :
    rationalTerm tau gamma a b (tau*a*b) accumulator =
      (gamma+tau*a)*(gamma+tau*b)*(tau*accumulator)-((gamma+tau*a)+(gamma+tau*b)) := by
  dsimp only [rationalTerm]
  ring

theorem product {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} (accepted : PairAccepted embed gamma w base aux) :
    base initializationRangeLayout.product = (Airbender.NativeInitializationOrdering.address w)[0]*
      (Airbender.NativeInitializationOrdering.address w)[1] := by
  have equation : (Airbender.NativeInitializationOrdering.address w)[0]*
      (Airbender.NativeInitializationOrdering.address w)[1]-base initializationRangeLayout.product = 0 := by
    simpa only [productTerm,one_mul] using accepted.product
  exact (sub_eq_zero.mp equation).symm

/-- Division-free pair equation, keeping duplicate poles rather than silently
    replacing this pair oracle by two separately enforced inverse oracles. -/
theorem factored {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} (accepted : PairAccepted embed gamma w base aux) :
    (gamma+embed (Airbender.NativeInitializationOrdering.address w)[0])*
      (gamma+embed (Airbender.NativeInitializationOrdering.address w)[1])*
      aux initializationRangeLayout.accumulator =
    (gamma+embed (Airbender.NativeInitializationOrdering.address w)[0])+
      (gamma+embed (Airbender.NativeInitializationOrdering.address w)[1]) := by
  have p := product embed gamma accepted
  have h := accepted.rational
  rw [p,map_mul] at h
  dsimp only [rationalTerm] at h
  linear_combination h

/-- A pole on one limb forces the other limb to the same pole. No division or
    nonzero hypothesis is smuggled into the source relation. -/
theorem pole_pair {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} (accepted : PairAccepted embed gamma w base aux)
    (pole : gamma+embed (Airbender.NativeInitializationOrdering.address w)[0] = 0) :
    gamma+embed (Airbender.NativeInitializationOrdering.address w)[1] = 0 := by
  have h := factored embed gamma accepted
  simpa only [pole,zero_mul,zero_add] using h.symm

theorem distinct_nonpoles {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} (accepted : PairAccepted embed gamma w base aux)
    (different : (Airbender.NativeInitializationOrdering.address w)[0] ≠
      (Airbender.NativeInitializationOrdering.address w)[1]) :
    gamma+embed (Airbender.NativeInitializationOrdering.address w)[0] ≠ 0 ∧
      gamma+embed (Airbender.NativeInitializationOrdering.address w)[1] ≠ 0 := by
  have h := factored embed gamma accepted
  constructor
  · intro pole
    have other := pole_pair embed gamma accepted pole
    apply different
    apply embed.injective
    linear_combination pole-other
  · intro pole
    have other : gamma+embed (Airbender.NativeInitializationOrdering.address w)[0] = 0 := by
      simpa only [pole,mul_zero,zero_mul,add_zero] using h.symm
    apply different
    apply embed.injective
    linear_combination other-pole

/-- Conditional inverse-sum reading of the checked division-free equation.
    The nonpole conditions are stated explicitly, never inferred at duplicates. -/
theorem inverse_sum {R : Type} [Field R] (embed : F →+* R) (gamma : R)
    {w : Nat → F} {base : BaseAuxiliaryColumn → F}
    {aux : Airbender.Blake2Worker.QuarticColumn → R} (accepted : PairAccepted embed gamma w base aux)
    (left : gamma+embed (Airbender.NativeInitializationOrdering.address w)[0] ≠ 0)
    (right : gamma+embed (Airbender.NativeInitializationOrdering.address w)[1] ≠ 0) :
    aux initializationRangeLayout.accumulator =
      (gamma+embed (Airbender.NativeInitializationOrdering.address w)[0])⁻¹+
      (gamma+embed (Airbender.NativeInitializationOrdering.address w)[1])⁻¹ := by
  have h := factored embed gamma accepted
  apply (mul_left_cancel₀ (mul_ne_zero left right))
  calc
    _ = (gamma+embed (Airbender.NativeInitializationOrdering.address w)[0])+
        (gamma+embed (Airbender.NativeInitializationOrdering.address w)[1]) := h
    _ = _ := by
      field_simp
      ring

/-- Pure source slice: a duplicated pole leaves this pair accumulator free.
    This states no complete native body, scalar-table sum or global acceptance. -/
theorem double_pole {R : Type} [CommRing R] (a accumulator : R) :
    productTerm 1 a a (a*a) = 0 ∧ rationalTerm 1 (-a) a a (a*a) accumulator = 0 := by
  constructor <;> dsimp only [productTerm,rationalTerm] <;> ring

theorem full_domain {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    (∀ i < initializationRangeLayout.traceLength-1,
      proof.base i initializationRangeLayout.product =
        (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0]*
        (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1]) ∧
    (∀ i < initializationRangeLayout.traceLength-1,
      (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0])*
        (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1])*
        proof.main.auxiliary i initializationRangeLayout.accumulator =
      (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0])+
        (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1])) :=
  ⟨fun i ordinary => product embed gamma (accepted.pairs i ordinary),
    fun i ordinary => factored embed gamma (accepted.pairs i ordinary)⟩
end Airbender.NativeInitializationRangeProofs
