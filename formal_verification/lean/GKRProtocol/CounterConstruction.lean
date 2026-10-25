import GKRProtocol.CounterPartition

namespace Airbender.Compiler
set_option warningAsError true
variable {R : Type} [CommRing R]

private theorem interleave_groups (keys : List K) (first second : K → List A) :
    (keys.flatMap (fun key => first key ++ second key)).Perm
      (keys.flatMap first ++ keys.flatMap second) := by
  induction keys with
  | nil => rfl
  | cons head tail proof =>
      simp only [List.flatMap_cons]
      apply (proof.append_left (first head ++ second head)).trans
      have middle : (second head ++ tail.flatMap first).Perm (tail.flatMap first ++ second head) :=
        List.perm_append_comm
      simpa only [List.append_assoc] using (middle.append_left (first head)).append_right (tail.flatMap second)

private theorem flatMap_singletons (keys : List K) (value : K → A) :
    keys.flatMap (fun key => [value key]) = keys.map value := by
  induction keys with
  | nil => rfl
  | cons head tail proof =>
      change value head :: tail.flatMap (fun key => [value key]) = value head :: tail.map value
      exact congrArg (List.cons (value head)) proof

def lookupCount [DecidableEq K] (key : K) (entries : List Q) (label : Q → K) (weight : Q → R) : R :=
  ((entries.filter (fun entry => decide (label entry = key))).map weight).sum

def lookupQueryTerms (entries : List Q) (label : Q → K) (weight : Q → R) (denominator : K → R) :
    List (RationalPair R) := entries.map (fun entry => RationalPair.leaf (weight entry) (denominator (label entry)))

def lookupSetupTerms [DecidableEq K] (keys : List K) (entries : List Q) (label : Q → K)
    (weight : Q → R) (denominator : K → R) : List (RationalPair R) :=
  keys.map (fun key => RationalPair.leaf (-lookupCount key entries label weight) (denominator key))

theorem lookupCount_hom {S : Type} [CommRing S] [DecidableEq K] (hom : S →+* R)
    (key : K) (entries : List Q) (label : Q → K) (weight : Q → S) :
    hom (lookupCount key entries label weight) = lookupCount key entries label (fun entry => hom (weight entry)) := by
  unfold lookupCount
  generalize entries.filter (fun entry => decide (label entry = key)) = selected
  induction selected with
  | nil => exact map_zero hom
  | cons head tail proof =>
      simpa only [List.map_cons, List.sum_cons, map_add] using
        congrArg (fun value => hom (weight head) + value) proof

/-- Construct multiplicities from the original weighted query occurrences.
The only membership premise supplies a setup-row witness for each query. -/
theorem canonicalLookupCounts_zero [DecidableEq K] (keys : List K) (entries : List Q) (label : Q → K)
    (weight : Q → R) (denominator : K → R) (unique : keys.Nodup)
    (covered : ∀ entry ∈ entries, label entry ∈ keys) :
    (lookupQueryTerms entries label weight denominator ++
      lookupSetupTerms keys entries label weight denominator).sum.numerator = 0 := by
  let weights := fun key => (entries.filter (fun entry => decide (label entry = key))).map weight
  let first := fun key => weightedLookupLeaves (denominator key) (weights key)
  let second := fun key => [RationalPair.leaf (-(weights key).sum) (denominator key)]
  have firstSame (key : K) : first key =
      (entries.filter (fun entry => decide (label entry = key))).map
        (fun entry => RationalPair.leaf (weight entry) (denominator (label entry))) := by
    simp only [first, weights, weightedLookupLeaves, List.map_map]
    apply List.map_congr_left
    intro entry member
    have same : label entry = key := of_decide_eq_true (List.mem_filter.mp member).2
    simp only [Function.comp_apply, same]
  have queryGroups : (keys.flatMap first).Perm (lookupQueryTerms entries label weight denominator) := by
    have partition := (query_partition keys entries label unique covered).map
      (fun entry => RationalPair.leaf (weight entry) (denominator (label entry)))
    rw [List.map_flatMap] at partition
    have same := congrArg (fun function => keys.flatMap function) (funext firstSame)
    rw [same]
    exact partition
  have setupGroups : keys.flatMap second = lookupSetupTerms keys entries label weight denominator := by
    exact flatMap_singletons keys _
  have grouped := interleave_groups keys first second
  rw [setupGroups] at grouped
  have coverage := grouped.trans (queryGroups.append_right (lookupSetupTerms keys entries label weight denominator))
  have zero : (keys.flatMap (fun key => first key ++ second key)).sum.numerator = 0 := by
    simpa only [List.flatMap_map, Function.comp_apply, first, second, balancedLookupGroup] using
      (groupedLookup_zero (keys.map (fun key => (denominator key, weights key))))
  exact (congrArg RationalPair.numerator coverage.sum_eq).symm.trans zero

end Airbender.Compiler
