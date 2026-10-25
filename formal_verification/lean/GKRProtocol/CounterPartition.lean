import GKRProtocol.CounterWitness

namespace Airbender.Compiler
set_option warningAsError true

private theorem flatMap_congr_on (items : List A) (first second : A → List B)
    (same : ∀ item ∈ items, first item = second item) : items.flatMap first = items.flatMap second := by
  induction items with
  | nil => rfl
  | cons head tail proof =>
      simp only [List.flatMap_cons]
      exact congrArg₂ (· ++ ·) (same head List.mem_cons_self)
        (proof (fun item member => same item (List.mem_cons_of_mem _ member)))

/-- Partition every query occurrence by its chosen setup-row witness. Keys are
unique, while queries and table values may repeat. -/
theorem query_partition [DecidableEq K] (keys : List K) (entries : List Q) (label : Q → K)
    (unique : keys.Nodup) (covered : ∀ entry ∈ entries, label entry ∈ keys) :
    (keys.flatMap (fun key => entries.filter (fun entry => decide (label entry = key)))).Perm entries := by
  induction keys generalizing entries with
  | nil =>
      cases entries with
      | nil => rfl
      | cons head tail =>
          have impossible := covered head List.mem_cons_self
          simp at impossible
  | cons head tail proof =>
      have split := List.nodup_cons.mp unique
      let remaining := entries.filter (fun entry => !decide (label entry = head))
      have remainingCovered : ∀ entry ∈ remaining, label entry ∈ tail := by
        intro entry member
        have original := List.mem_filter.mp member
        have different : label entry ≠ head := by simpa using original.2
        exact (List.mem_cons.mp (covered entry original.1)).resolve_left different
      have filtered (key : K) (member : key ∈ tail) :
          entries.filter (fun entry => decide (label entry = key)) =
            remaining.filter (fun entry => decide (label entry = key)) := by
        have different : key ≠ head := by
          intro same
          exact split.1 (same ▸ member)
        unfold remaining
        rw [List.filter_filter]
        apply List.filter_congr
        intro entry _
        by_cases matched : label entry = key
        · simp [matched, different]
        · simp [matched]
      have tailSame := flatMap_congr_on tail
        (fun key => entries.filter (fun entry => decide (label entry = key)))
        (fun key => remaining.filter (fun entry => decide (label entry = key))) filtered
      simp only [List.flatMap_cons]
      rw [tailSame]
      exact ((proof remaining split.2 remainingCovered).append_left
        (entries.filter (fun entry => decide (label entry = head)))).trans
          (List.filter_append_perm (fun entry => decide (label entry = head)) entries)

end Airbender.Compiler
