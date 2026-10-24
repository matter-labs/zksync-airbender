import GKRProtocol.BaseEncoding

namespace Airbender.Compiler
set_option warningAsError true

theorem List.map_range_getD (items : List α) (fallback : α) :
    ((List.range items.length).map (fun index => (items[index]?).getD fallback)) = items := by
  induction items with
  | nil => rfl
  | cons first rest proof =>
      simpa [List.range_succ_eq_map, Function.comp_def] using
        congrArg (first :: ·) proof

/-- A native reduction and a checked exact permutation of original request
labels determine the complete source sum, including its designated setup term.
No division or probabilistic challenge assumption is involved. -/
theorem LookupTree.translate_output [CommRing R] (tree : LookupTree Nat)
    (primitive : Nat → RationalPair R) (output : RationalPair R)
    (native : output = (tree.leaves.map primitive).sum)
    (source : List (RationalPair R)) (label : Nat → Nat)
    (fields : ∀ index ∈ tree.leaves, primitive index = (source[label index]?).getD 0)
    (coverage : (tree.leaves.map label).Perm (List.range source.length)) :
    output = source.sum := by
  have same : tree.leaves.map primitive =
      (tree.leaves.map label).map (fun index => (source[index]?).getD 0) := by
    rw [List.map_map]
    exact List.map_congr_left fields
  rw [same, (coverage.map (fun index => (source[index]?).getD 0)).sum_eq,
    List.map_range_getD] at native
  exact native

end Airbender.Compiler
