import GKRProtocol.RationalSemantics

namespace Airbender.Compiler
set_option warningAsError true
variable {R : Type} [CommRing R]

def weightedLookupLeaves (denominator : R) (weights : List R) : List (RationalPair R) :=
  weights.map (fun weight => RationalPair.leaf weight denominator)

/-- A division-free invariant, including the empty group and zero denominator. -/
theorem weightedLookupLeaves_value (denominator : R) (weights : List R) :
    (weightedLookupLeaves denominator weights).sum.numerator * denominator =
        weights.sum * denominator ^ weights.length ∧
      (weightedLookupLeaves denominator weights).sum.denominator = denominator ^ weights.length := by
  induction weights with
  | nil =>
      simp only [weightedLookupLeaves, List.map_nil, List.sum_nil, List.length_nil, pow_zero, zero_mul]
      change (0 : R) * denominator = 0 ∧ (1 : R) = 1
      exact ⟨zero_mul _, rfl⟩
  | cons head tail proof =>
      constructor
      · change (head * (weightedLookupLeaves denominator tail).sum.denominator +
          denominator * (weightedLookupLeaves denominator tail).sum.numerator) * denominator =
          (head + tail.sum) * denominator ^ (tail.length + 1)
        rw [proof.2, pow_succ]
        calc
          _ = head * (denominator ^ tail.length * denominator) +
              denominator * ((weightedLookupLeaves denominator tail).sum.numerator * denominator) := by ring
          _ = _ := by rw [proof.1]; ring
      · change denominator * (weightedLookupLeaves denominator tail).sum.denominator =
          denominator ^ (tail.length + 1)
        rw [proof.2, pow_succ, mul_comm]

def balancedLookupGroup (denominator : R) (weights : List R) : List (RationalPair R) :=
  weightedLookupLeaves denominator weights ++ [RationalPair.leaf (-weights.sum) denominator]

/-- The canonical setup multiplicity cancels every occurrence, including
duplicates and weighted queries. No challenge is assumed nonzero. -/
theorem balancedLookupGroup_zero (denominator : R) (weights : List R) :
    (balancedLookupGroup denominator weights).sum.numerator = 0 := by
  have invariant := weightedLookupLeaves_value denominator weights
  simp only [balancedLookupGroup, List.sum_append, List.sum_singleton]
  change (weightedLookupLeaves denominator weights).sum.numerator * denominator +
    (weightedLookupLeaves denominator weights).sum.denominator * (-weights.sum) = 0
  rw [invariant.1, invariant.2]
  ring

theorem groupedLookup_zero (groups : List (R × List R)) :
    (groups.flatMap (fun group => balancedLookupGroup group.1 group.2)).sum.numerator = 0 := by
  induction groups with
  | nil => rfl
  | cons group rest proof =>
      simp only [List.flatMap_cons, List.sum_append]
      change (balancedLookupGroup group.1 group.2).sum.numerator * _ +
        (balancedLookupGroup group.1 group.2).sum.denominator *
          (rest.flatMap (fun group => balancedLookupGroup group.1 group.2)).sum.numerator = 0
      rw [balancedLookupGroup_zero, proof]
      ring

theorem lookupCounterWitness (terms : List (RationalPair R)) (groups : List (R × List R))
    (coverage : terms.Perm (groups.flatMap (fun group => balancedLookupGroup group.1 group.2))) :
    terms.sum.numerator = 0 := by
  rw [coverage.sum_eq]
  exact groupedLookup_zero groups

end Airbender.Compiler
