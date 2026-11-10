import Airbender.Proofs.GKRProtocol.CounterConstruction

namespace Airbender.Compiler
set_option warningAsError true
variable {R : Type} [CommRing R]

theorem RationalPair.sum_numerator_zero (terms : List (RationalPair R))
    (zero : ∀ term ∈ terms, term.numerator = 0) : terms.sum.numerator = 0 := by
  induction terms with
  | nil => rfl
  | cons head tail proof =>
      change head.numerator * tail.sum.denominator + head.denominator * tail.sum.numerator = 0
      rw [zero head List.mem_cons_self, proof (fun term member => zero term (List.mem_cons_of_mem _ member))]
      ring

theorem RationalPair.append_numerator_zero (first second : List (RationalPair R))
    (firstZero : first.sum.numerator = 0) (secondZero : second.sum.numerator = 0) :
    (first ++ second).sum.numerator = 0 := by
  rw [List.sum_append]
  change first.sum.numerator * second.sum.denominator + first.sum.denominator * second.sum.numerator = 0
  rw [firstZero, secondZero]
  ring

/-- Disabled queries need no table-row witness, and their payload denominator
is arbitrary. This covers the compiler's execution-masked decoder query. -/
theorem canonicalMaskedLookupCounts_zero [DecidableEq K] (keys : List K) (entries : List Q)
    (enabled : Q → Bool) (label : Q → K) (weight : Q → R)
    (queryDenominator : Q → R) (tableDenominator : K → R) (unique : keys.Nodup)
    (covered : ∀ entry ∈ entries.filter enabled, label entry ∈ keys)
    (matching : ∀ entry ∈ entries.filter enabled, queryDenominator entry = tableDenominator (label entry))
    (disabled : ∀ entry ∈ entries.filter (fun entry => !enabled entry), weight entry = 0) :
    (entries.map (fun entry => RationalPair.leaf (weight entry) (queryDenominator entry)) ++
      lookupSetupTerms keys (entries.filter enabled) label weight tableDenominator).sum.numerator = 0 := by
  let active := entries.filter enabled
  let inactive := entries.filter (fun entry => !enabled entry)
  let leaf := fun entry => RationalPair.leaf (weight entry) (queryDenominator entry)
  let setup := lookupSetupTerms keys active label weight tableDenominator
  have activeSame : active.map leaf = lookupQueryTerms active label weight tableDenominator := by
    apply List.map_congr_left
    intro entry member
    exact congrArg (RationalPair.leaf (weight entry)) (matching entry member)
  have activeZero : (active.map leaf ++ setup).sum.numerator = 0 := by
    rw [activeSame]
    exact canonicalLookupCounts_zero keys active label weight tableDenominator unique covered
  have inactiveZero : (inactive.map leaf).sum.numerator = 0 := by
    apply RationalPair.sum_numerator_zero
    intro term member
    obtain ⟨entry, included, same⟩ := List.mem_map.mp member
    rw [← same]
    exact disabled entry included
  have partition : (active.map leaf ++ inactive.map leaf).Perm (entries.map leaf) := by
    simpa only [List.map_append] using (List.filter_append_perm enabled entries).map leaf
  have swap : ((active.map leaf ++ inactive.map leaf) ++ setup).Perm ((active.map leaf ++ setup) ++ inactive.map leaf) := by
    have middle : (inactive.map leaf ++ setup).Perm (setup ++ inactive.map leaf) := List.perm_append_comm
    simpa only [List.append_assoc] using middle.append_left (active.map leaf)
  have coverage := (partition.symm.append_right setup).trans swap
  exact (congrArg RationalPair.numerator coverage.sum_eq).trans
    (RationalPair.append_numerator_zero _ _ activeZero inactiveZero)

end Airbender.Compiler
