import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

namespace Airbender.Trace.FiniteFootprint

/-! Extend an exact finite token balance by an unchanged part of a domain.
The maps may identify different domain elements; no injectivity, token equality
instance, memory semantics or sampled-product argument is required. -/

private theorem commute_middle {β : Type*} (front middle back : List β) :
    ((front ++ middle) ++ back).Perm ((front ++ back) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := back)).append_left front

/-- A finite balance extends across any explicitly partitioned unchanged rest. -/
theorem balance_of_partition {α β : Type*}
    (domain touched rest : List α) (old new : α → β) (reads writes : List β)
    (partition : domain.Perm (touched ++ rest))
    (frame : ∀ x ∈ rest, new x = old x)
    (balance : (touched.map old ++ writes).Perm (touched.map new ++ reads)) :
    (domain.map old ++ writes).Perm (domain.map new ++ reads) := by
  have stable : rest.map old = rest.map new := by
    apply List.map_congr_left
    intro x member
    exact (frame x member).symm
  have start : (domain.map old ++ writes).Perm
      ((touched.map old ++ rest.map old) ++ writes) := by
    simpa only [List.map_append] using (partition.map old).append_right writes
  have middle : ((touched.map old ++ writes) ++ rest.map old).Perm
      ((touched.map new ++ reads) ++ rest.map new) := by
    rw [← stable]
    exact balance.append_right _
  have finish : ((touched.map new ++ rest.map new) ++ reads).Perm
      (domain.map new ++ reads) := by
    simpa only [List.map_append] using (partition.map new).symm.append_right reads
  exact start.trans ((commute_middle _ _ _).trans
    (middle.trans ((commute_middle _ _ _).symm.trans finish)))

/-- Without distinctness assumptions, balance the actual touched occurrences in
    the domain. Multiplicity is retained by filtering, not discarded as a set. -/
theorem balance_of_filter {α β : Type*} [DecidableEq α]
    (domain touched : List α) (old new : α → β) (reads writes : List β)
    (frame : ∀ x ∈ domain, x ∉ touched → new x = old x)
    (balance :
      ((domain.filter fun x => decide (x ∈ touched)).map old ++ writes).Perm
      ((domain.filter fun x => decide (x ∈ touched)).map new ++ reads)) :
    (domain.map old ++ writes).Perm (domain.map new ++ reads) := by
  let active := domain.filter fun x => decide (x ∈ touched)
  let rest := domain.filter fun x => !decide (x ∈ touched)
  have partition : (active ++ rest).Perm domain :=
    List.filter_append_perm (fun x => decide (x ∈ touched)) domain
  apply balance_of_partition domain active rest old new reads writes partition.symm
  · intro x member
    have actual : x ∈ domain ∧ x ∉ touched := by simpa [rest] using member
    exact frame x actual.1 actual.2
  · exact balance

/-- A distinct finite footprint inside a distinct domain suffices: the premise
    checks the small supplied touched list, not a computed large-domain filter. -/
theorem balance_of_nodup {α β : Type*} [DecidableEq α]
    (domain touched : List α) (old new : α → β) (reads writes : List β)
    (domainNodup : domain.Nodup) (touchedNodup : touched.Nodup)
    (subset : touched ⊆ domain)
    (frame : ∀ x ∈ domain, x ∉ touched → new x = old x)
    (balance : (touched.map old ++ writes).Perm (touched.map new ++ reads)) :
    (domain.map old ++ writes).Perm (domain.map new ++ reads) := by
  let active := domain.filter fun x => decide (x ∈ touched)
  have unique : active.Nodup := List.Nodup.filter _ domainNodup
  have members (x : α) : x ∈ active ↔ x ∈ touched := by
    constructor
    · intro member
      have actual : x ∈ domain ∧ x ∈ touched := by simpa [active] using member
      exact actual.2
    · intro member
      have inside : x ∈ domain := subset member
      simp [active, inside, member]
  have selected : active.Perm touched := by
    apply List.perm_iff_count.mpr
    intro x
    by_cases member : x ∈ touched
    · exact (List.count_eq_one_of_mem unique ((members x).mpr member)).trans
        (List.count_eq_one_of_mem touchedNodup member).symm
    · have absent : x ∉ active := fun present => member ((members x).mp present)
      exact (List.count_eq_zero.mpr absent).trans (List.count_eq_zero.mpr member).symm
  apply balance_of_filter domain touched old new reads writes frame
  exact ((selected.map old).append_right writes).trans
    (balance.trans ((selected.map new).symm.append_right reads))

end Airbender.Trace.FiniteFootprint
