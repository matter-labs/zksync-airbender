module
public import Human.Trace.Machine.Segmentation
public import Proven.Trace.Machine.UnifiedRequests

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Delegation
set_option warningAsError true

open Classical in
theorem disjoint_filter_flatMap_count {α β : Type} [BEq α] [LawfulBEq α] (rows : List α) (windows : List β)
    (select : β → α → Bool)
    (separated : windows.Pairwise (fun first second => ∀ row,
      ¬ (select first row = true ∧ select second row = true))) (row : α) :
    (windows.flatMap fun window => rows.filter (select window)).count row =
      if ∃ window ∈ windows, select window row = true then rows.count row else 0 := by
  classical
  induction windows with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨disjoint, rest⟩ := List.pairwise_cons.mp separated
    rw [List.flatMap_cons, List.count_append, ih rest]
    by_cases chosen : select head row = true
    · have absent : ¬ ∃ window ∈ tail, select window row = true := by
        rintro ⟨window, member, selected⟩
        exact disjoint window member row ⟨chosen, selected⟩
      rw [List.count_filter chosen]
      simp [chosen, absent]
    · have zero : (rows.filter (select head)).count row = 0 := by
        apply List.count_eq_zero.mpr
        simp [chosen]
      rw [zero]
      simp [chosen]

/-- Ordered protocol intervals assign each selected request to one window. -/
theorem hash_window_unique {windows : List HashWindow}
    (separated : windows.Pairwise (fun first second => first.upper ≤ second.lower))
    {first second : HashWindow} (one : first ∈ windows) (two : second ∈ windows)
    {request : Requests.Request p} (firstRange : first.select request = true) (secondRange : second.select request = true) :
    first = second := by
  have firstBounds := of_decide_eq_true firstRange
  have secondBounds := of_decide_eq_true secondRange
  induction windows with
  | nil => cases one
  | cons head tail ih =>
    obtain ⟨before, rest⟩ := List.pairwise_cons.mp separated
    rcases List.mem_cons.mp one with firstHead | firstTail
    · rcases List.mem_cons.mp two with secondHead | secondTail
      · exact firstHead.trans secondHead.symm
      · rw [firstHead] at firstBounds
        have bound := before second secondTail
        omega
    · rcases List.mem_cons.mp two with secondHead | secondTail
      · rw [secondHead] at secondBounds
        have bound := before first firstTail
        omega
      · exact ih rest firstTail secondTail

open Classical in
/-- Exact request coverage preserves every hash occurrence and its multiplicity. -/
theorem hash_request_partition {calls : List (Requests.Request p)} {windows : List HashWindow}
    (profile : HashWindowProfile calls windows) :
    (windows.flatMap (windowRequests calls)).Perm (hashRequests calls) := by
  classical
  have disjoint : windows.Pairwise (fun first second => ∀ request : Requests.Request p,
      ¬ (first.select request = true ∧ second.select request = true)) := by
    apply profile.separated.imp
    intro first second order request both
    have firstBounds := of_decide_eq_true both.1
    have secondBounds := of_decide_eq_true both.2
    omega
  apply List.perm_iff_count.mpr
  intro request
  have count := disjoint_filter_flatMap_count calls windows HashWindow.select disjoint request
  change (windows.flatMap (windowRequests calls)).count request =
    (if ∃ window ∈ windows, window.select request = true then calls.count request else 0) at count
  rw [count]
  by_cases member : request ∈ calls
  · have selection := (profile.coverage request member).symm
    by_cases wanted : request.csr ≠ Requests.csr .bigint
    · rw [ite_eq_left (selection.mpr wanted)]
      simpa only [hashRequests] using (List.count_filter
        (p := fun actual : Requests.Request p => decide (actual.csr ≠ Requests.csr .bigint))
        (a := request) (l := calls) (decide_eq_true wanted)).symm
    · rw [ite_eq_right (fun selected => wanted (selection.mp selected))]
      symm
      apply List.count_eq_zero.mpr
      simp [hashRequests, wanted]
  · have absent : request ∉ hashRequests calls := fun inside => member (List.mem_of_mem_filter inside)
    rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr absent]
    split <;> rfl

/-- Full native matching transports public caller windows to all submitted hash workers. -/
theorem hash_segmentation_of_matching {calls fulfilled : List (Requests.Request p)} {windows : List HashWindow}
    (matching : calls.Perm fulfilled) (profile : HashWindowProfile calls windows)
    (live : ∀ request ∈ fulfilled, Requests.Live request) : IssuedHashSegmentation fulfilled windows := by
  have transported : HashWindowProfile fulfilled windows := by
    refine ⟨profile.separated, fun request member => profile.coverage request (matching.mem_iff.mpr member), ?_, ?_⟩
    · intro window member
      exact (matching.filter window.select).length_eq.symm.trans (profile.counts window member)
    · intro window member request included
      exact profile.families window member request ((matching.filter window.select).mem_iff.mpr included)
  have partition := hash_request_partition transported
  refine ⟨partition, ?_, ?_, transported.families, fun request member => live request (List.mem_of_mem_filter member)⟩
  · intro request member
    have source := List.mem_of_mem_filter member
    have hash := of_decide_eq_true (List.mem_filter.mp member).2
    obtain ⟨window, included, selected⟩ := (transported.coverage request source).mp hash
    exact ⟨window, ⟨included, selected⟩, fun other present =>
      hash_window_unique transported.separated present.1 included present.2 selected⟩
  · have length := partition.length_eq
    rw [List.length_flatMap] at length
    have counts : windows.map (fun window => (windowRequests fulfilled window).length) =
        windows.map (fun window => window.protocol.kinds.length) := List.map_congr_left transported.counts
    rw [counts] at length
    exact length

end Airbender.Trace.Machine.Proofs
