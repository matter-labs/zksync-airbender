module
public import Proven.Trace.MemoryPaths
public import Human.Helpers.Core.ExternalStream

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
variable {α : Type}

/-- Count external reads strictly before a native boundary clock. -/
def readIndexAt (rows : List α) (clock : α → Nat) (read : α → Bool) (tick : Nat) : Nat :=
  (rows.filter fun row => read row && decide (clock row < tick)).length

/-- The boundary count is the reviewed external stream index at every row. -/
theorem read_index_at_row (rows : List α) (clock : α → Nat) (read : α → Bool) (row : α) :
    readIndexAt rows clock read (clock row) = ExternalStream.index clock read rows row := rfl

/-- Pointwise disjoint indicator sums give the corresponding filter lengths. -/
theorem split_filter_lengths (rows : List α) (total left right : α → Bool)
    (parts : ∀ row ∈ rows, (if total row then 1 else 0 : Nat) =
      (if left row then 1 else 0) + (if right row then 1 else 0)) :
    (rows.filter total).length = (rows.filter left).length + (rows.filter right).length := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    have first := parts head List.mem_cons_self
    have rest := ih (fun row member => parts row (List.mem_cons_of_mem head member))
    cases a : total head <;> cases b : left head <;> cases c : right head <;> simp_all <;> omega

/-- Each four-tick CPU cycle consumes exactly its selected external read. -/
theorem read_index_cycle (rows : List α) (clock : α → Nat) (read : α → Bool)
    (unique : (rows.map clock).Nodup) (aligned : ∀ row ∈ rows, clock row % 4 = 0)
    {row : α} (member : row ∈ rows) :
    readIndexAt rows clock read (clock row + 4) =
      readIndexAt rows clock read (clock row) + if read row then 1 else 0 := by
  have split := split_filter_lengths rows
    (fun source => read source && decide (clock source < clock row + 4))
    (fun source => read source && decide (clock source < clock row))
    (fun source => read source && decide (clock source = clock row)) (by
      intro source included
      have current := aligned row member
      have previous := aligned source included
      cases selected : read source with
      | false => simp
      | true =>
        simp only [Bool.true_and, decide_eq_true_eq]
        split_ifs <;> omega)
  have selected : (rows.filter fun source => read source && decide (clock source = clock row)).length =
      if read row then 1 else 0 := by
    have same : (rows.filter fun source => read source && decide (clock source = clock row)) =
        (rows.filter fun source => decide (clock source = clock row)).filter read := by
      rw [List.filter_filter]
    rw [same, Trace.Proofs.key_filter_singleton clock unique member]
    cases value : read row <;> simp [value]
  exact split.trans (congrArg ((readIndexAt rows clock read (clock row)) + ·) selected)

/-- A public initial clock below every row has no earlier external reads. -/
theorem read_index_initial (rows : List α) (clock : α → Nat) (read : α → Bool) (initial : Nat)
    (floor : ∀ row ∈ rows, initial ≤ clock row) : readIndexAt rows clock read initial = 0 := by
  have empty : (rows.filter fun row => read row && decide (clock row < initial)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member selected
    have both : read row = true ∧ clock row < initial := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using selected
    have earlier := both.2
    have bound := floor row member
    omega
  simp only [readIndexAt, empty, List.length_nil]

end Airbender.Trace.Machine.Proofs
