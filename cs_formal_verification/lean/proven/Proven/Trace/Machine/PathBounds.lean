module
public import Proven.Trace.Machine.MemoryClocks
public import Proven.Trace.Paths

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The first list element precedes each later element in a pairwise relation. -/
theorem head_relation {α : Type} {relation : α → α → Prop} {values : List α} {first value : α}
    (head : values.head? = some first) (ordered : values.Pairwise relation) (member : value ∈ values) :
    first = value ∨ relation first value := by
  cases values with
  | nil => simp at head
  | cons a rest =>
    have same : a = first := by simpa using head
    subst first
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl rfl
    · exact Or.inr (List.rel_of_pairwise_cons ordered present)

/-- Every clock on a strictly ordered path lies between its endpoints. -/
theorem ordered_clock_bounds {values : List Nat} {first last value : Nat}
    (head : values.head? = some first) (endPoint : values.getLast? = some last)
    (ordered : values.Pairwise (· < ·)) (member : value ∈ values) : first ≤ value ∧ value ≤ last := by
  have lower := head_relation head ordered member
  have upper := head_relation (by simpa using endPoint : values.reverse.head? = some last)
    (List.pairwise_reverse.mpr ordered) (List.mem_reverse.mpr member)
  constructor
  · rcases lower with same | less <;> omega
  · rcases upper with same | less <;> omega

/-- Native state matching bounds every instruction cycle by the public initial and terminal clocks. -/
theorem cpu_cycle_clock_bounds {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus Kind} (member : row ∈ trace.rows) :
    (timeOfPair trace.initial.timestamp).value ≤ row.clock ∧
      (decodeTimestamp row.assignment row.columns.finalTime).value ≤ (timeOfPair trace.terminal.timestamp).value := by
  obtain ⟨path, properties⟩ := state_path_checks (by decide) (by decide) constraints states initial aligned
  let rank := fun state : PCState.State babyBearModulus => (timeOfPair state.timestamp).value
  have clocks := state_clock_inputs (by decide) (by decide) constraints states initial aligned
  have ordered := rank_ordered rank path (by
    intro edge present
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp (properties.2.2.1.mem_iff.mp present)
    have advance := ClockLaws.advance (by decide) (by decide) trace.rom source (constraints source included) (clocks source included).1
    change (decodeTimestamp source.assignment source.columns.initialTime).value <
      (decodeTimestamp source.assignment source.columns.finalTime).value
    omega)
  have head : (path.map rank).head? = some (rank trace.initial) := by simp [properties.1]
  have last : (path.map rank).getLast? = some (rank trace.terminal) := by simp [properties.2.1]
  have edge : (row.start, row.finish) ∈ path.zip path.tail :=
    properties.2.2.1.mem_iff.mpr (List.mem_map.mpr ⟨row, member, rfl⟩)
  have nodes := List.of_mem_zip edge
  have lower := ordered_clock_bounds head last ordered (List.mem_map.mpr ⟨row.start, nodes.1, rfl⟩)
  have upper := ordered_clock_bounds head last ordered
    (List.mem_map.mpr ⟨row.finish, List.mem_of_mem_tail nodes.2, rfl⟩)
  exact ⟨lower.1, upper.2⟩

end Airbender.Trace.Machine.Proofs
