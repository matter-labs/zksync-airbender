import Clean.Circuit.Operations
import Airbender.Review.RangeChecks

namespace Airbender.Verification

/-- A native Clean sublist inherits satisfaction from the full artifact. -/
theorem holds_of_sublist {F : Type} [FiniteField F]
    {source target : List (_root_.FlatOperation F)} {env : _root_.Environment F}
    (h : _root_.FlatOperation.ConstraintsHoldFlat env source)
    (subset : target.Sublist source) :
    _root_.FlatOperation.ConstraintsHoldFlat env target := by
  induction subset with
  | slnil => trivial
  | @cons small large a subset ih =>
    cases a <;> simp only [FlatOperation.ConstraintsHoldFlat] at h
    all_goals exact ih (by first | exact h.2 | exact h)
  | @cons_cons small large a subset ih =>
    cases a <;> simp only [FlatOperation.ConstraintsHoldFlat] at h ⊢
    all_goals first | exact ⟨h.1, ih h.2⟩ | exact ih h

theorem holds_append {F : Type} [FiniteField F]
    {left right : List (_root_.FlatOperation F)} {env : _root_.Environment F}
    (hl : _root_.FlatOperation.ConstraintsHoldFlat env left)
    (hr : _root_.FlatOperation.ConstraintsHoldFlat env right) :
    _root_.FlatOperation.ConstraintsHoldFlat env (left ++ right) := by
  induction left using FlatOperation.induct <;>
    simp_all [FlatOperation.ConstraintsHoldFlat]

/-- Extract an assertion using Clean's own constraint-satisfaction theorem. -/
theorem assertion_of_holds {F : Type} [FiniteField F]
    {ops : List (_root_.FlatOperation F)} {env : _root_.Environment F}
    (h : _root_.FlatOperation.ConstraintsHoldFlat env ops)
    (i : Fin (_root_.FlatOperation.constraints ops).length) :
    ((_root_.FlatOperation.constraints ops).get i).eval env = 0 :=
  (_root_.FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).1 _ (List.get_mem _ _)

/-- Extract a lookup using the same native Clean satisfaction relation. -/
theorem lookup_of_holds {F : Type} [FiniteField F]
    {ops : List (_root_.FlatOperation F)} {env : _root_.Environment F}
    (h : _root_.FlatOperation.ConstraintsHoldFlat env ops)
    (i : Fin (_root_.FlatOperation.lookups ops).length) :
    ((_root_.FlatOperation.lookups ops).get i).Contains env :=
  (_root_.FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).2 _ (List.get_mem _ _)

/-- Static-table membership gives a bound on the query's canonical representative. -/
theorem range16_bound {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : _root_.Environment (ZMod p)} (h : (range16 entry).Contains env) :
    (entry.eval env).val < Arithmetic.limbBase := by
  have hs : (range16 entry).Soundness env :=
    (range16 entry).table.imply_soundness _ _ h
  exact (Lookup.soundess_def_field range16Table env entry).mp hs

/-- Construct native table membership from a canonical bound, for concrete
    boundary and inactive-row checks. -/
theorem range16_contains {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : _root_.Environment (ZMod p)} (h : (entry.eval env).val < Arithmetic.limbBase) :
    (range16 entry).Contains env := by
  have hc : (range16 entry).Completeness env :=
    (Lookup.completeness_def_field range16Table env entry).mpr h
  exact (range16 entry).table.implied_by_completeness _ _ hc

/-- The carry queries use the same native range-table semantics at 13 bits. -/
theorem range13_bound {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : _root_.Environment (ZMod p)} (h : (range13 entry).Contains env) :
    (entry.eval env).val < 8192 := by
  have hs := (range13 entry).table.imply_soundness _ _ h
  exact (Lookup.soundess_def_field range13Table env entry).mp hs

theorem range13_contains {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : _root_.Environment (ZMod p)} (h : (entry.eval env).val < 8192) :
    (range13 entry).Contains env := by
  have hc := (Lookup.completeness_def_field range13Table env entry).mpr h
  exact (range13 entry).table.implied_by_completeness _ _ hc

end Airbender.Verification
