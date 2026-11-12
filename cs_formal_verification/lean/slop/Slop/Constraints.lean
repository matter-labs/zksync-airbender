module
public import CleanCore.Circuit.Operations
public import Human.Helpers.Tables.Range
public import Slop.CleanCore.Circuit.Operations
public import Slop.CleanCore.Circuit.Lookup

@[expose] public section

namespace Airbender.Verification

/-- A native Clean sublist inherits satisfaction from the full artifact. -/
theorem holds_of_sublist {F : Type} [Field F]
    {source target : List (Airbender.FlatOperation F)} {env : Airbender.Environment F}
    (h : Airbender.FlatOperation.ConstraintsHoldFlat env source)
    (subset : target.Sublist source) :
    Airbender.FlatOperation.ConstraintsHoldFlat env target := by
  induction subset with
  | slnil => trivial
  | @cons small large a subset ih =>
    cases a <;> simp only [FlatOperation.ConstraintsHoldFlat] at h
    all_goals exact ih h.2
  | @cons_cons small large a subset ih =>
    cases a <;> simp only [FlatOperation.ConstraintsHoldFlat] at h ⊢
    all_goals exact ⟨h.1, ih h.2⟩

theorem holds_append {F : Type} [Field F]
    {left right : List (Airbender.FlatOperation F)} {env : Airbender.Environment F}
    (hl : Airbender.FlatOperation.ConstraintsHoldFlat env left)
    (hr : Airbender.FlatOperation.ConstraintsHoldFlat env right) :
    Airbender.FlatOperation.ConstraintsHoldFlat env (left ++ right) := by
  induction left using FlatOperation.induct <;>
    simp_all [FlatOperation.ConstraintsHoldFlat]

/-- Extract an assertion using Clean's own constraint-satisfaction theorem. -/
theorem assertion_of_holds {F : Type} [Field F]
    {ops : List (Airbender.FlatOperation F)} {env : Airbender.Environment F}
    (h : Airbender.FlatOperation.ConstraintsHoldFlat env ops)
    (i : Fin (Airbender.FlatOperation.constraints ops).length) :
    ((Airbender.FlatOperation.constraints ops).get i).eval env = 0 :=
  (Airbender.FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).1 _ (List.get_mem _ _)

/-- Extract a lookup using the same native Clean satisfaction relation. -/
theorem lookup_of_holds {F : Type} [Field F]
    {ops : List (Airbender.FlatOperation F)} {env : Airbender.Environment F}
    (h : Airbender.FlatOperation.ConstraintsHoldFlat env ops)
    (i : Fin (Airbender.FlatOperation.lookups ops).length) :
    ((Airbender.FlatOperation.lookups ops).get i).Contains env :=
  (Airbender.FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).2 _ (List.get_mem _ _)

/-- Static-table membership gives a bound on the query's canonical representative. -/
theorem range16_bound {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : Airbender.Environment (ZMod p)} (h : (range16 entry).Contains env) :
    (entry.eval env).val < Arithmetic.limbBase := by
  have hs : (range16 entry).Soundness env :=
    (range16 entry).table.imply_soundness _ _ h
  exact (Lookup.soundess_def_field range16Table env entry).mp hs

/-- Construct native table membership from a canonical bound, for concrete
    boundary and inactive-row checks. -/
theorem range16_contains {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : Airbender.Environment (ZMod p)} (h : (entry.eval env).val < Arithmetic.limbBase) :
    (range16 entry).Contains env := by
  have hc : (range16 entry).Completeness env :=
    (Lookup.completeness_def_field range16Table env entry).mpr h
  exact (range16 entry).table.implied_by_completeness _ _ hc

/-- The carry queries use the same native range-table semantics at 13 bits. -/
theorem range13_bound {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : Airbender.Environment (ZMod p)} (h : (range13 entry).Contains env) :
    (entry.eval env).val < 8192 := by
  have hs := (range13 entry).table.imply_soundness _ _ h
  exact (Lookup.soundess_def_field range13Table env entry).mp hs

theorem range13_contains {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : Airbender.Environment (ZMod p)} (h : (entry.eval env).val < 8192) :
    (range13 entry).Contains env := by
  have hc := (Lookup.completeness_def_field range13Table env entry).mpr h
  exact (range13 entry).table.implied_by_completeness _ _ hc

end Airbender.Verification
