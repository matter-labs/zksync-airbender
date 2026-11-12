module
public import Proven.Trace.MemoryPaths

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Trace.Proofs
set_option warningAsError true

/-- Row filtering commutes with expansion to row event lists. -/
theorem filter_flatMap_rows (rows : List α) (predicate : α → Bool) (events : α → List β) :
    (rows.filter predicate).flatMap events = rows.flatMap (fun row => if predicate row then events row else []) := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    split <;> simp_all

/-- Filtering event lists by a unique occurrence keeps exactly that occurrence's full event list. -/
theorem event_group_single {α Key : Type} [DecidableEq Key] (rows : List α) (rank : α → Key) (events : α → List MemoryAccess)
    (keep : MemoryAccess → Bool) (unique : (rows.map rank).Nodup)
    {row : α} (member : row ∈ rows)
    (selected : ∀ source ∈ rows, ∀ event ∈ events source, keep event = true ↔ source = row) :
    (rows.flatMap events).filter keep = events row := by
  have singleton := key_filter_singleton rank unique member
  have filtered : ∀ source ∈ rows, (events source).filter keep =
      if decide (rank source = rank row) then events source else [] := by
    intro source included
    by_cases same : rank source = rank row
    · have equal := List.inj_on_of_nodup_map unique included member same
      subst source
      simp only [decide_true, ite_true]
      exact List.filter_eq_self.mpr (fun event present => (selected row member event present).mpr rfl)
    · simp only [same, decide_false, Bool.false_eq_true, ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      exact same (congrArg rank ((selected source included event present).mp actual))
  rw [List.filter_flatMap]
  calc
    _ = rows.flatMap (fun source => if decide (rank source = rank row) then events source else []) :=
      List.flatMap_congr filtered
    _ = (rows.filter fun source => decide (rank source = rank row)).flatMap events :=
      (filter_flatMap_rows _ _ _).symm
    _ = events row := by rw [singleton]; simp

end Airbender.Trace.Machine.Proofs
