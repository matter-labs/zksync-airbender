import Airbender.Review.Helpers.Context.PaddingBoundary.Model

namespace Airbender.PaddingBoundary.Proofs
open Trace
set_option warningAsError true

@[simp] theorem mask_zero [Ring R] (input : R) : mask (0 : R) input = 1 := by
  simp [mask]

@[simp] theorem mask_one [Ring R] (input : R) : mask (1 : R) input = input := by
  simp [mask]

@[simp] theorem contribution_zero [Ring R] [Nontrivial R]
    [DecidableEq R] (value : α) : contribution (0 : R) value = none := by
  simp [contribution]

@[simp] theorem contribution_one [One R] [DecidableEq R] (value : α) :
    contribution (1 : R) value = some value := by
  simp [contribution]

theorem evaluate_contribution [Ring R] [Nontrivial R] [DecidableEq R]
    (execute : R) (boolean : execute = 0 ∨ execute = 1) (encode : α → R) (value : α) :
    evaluate encode (contribution execute value) = mask execute (encode value) := by
  rcases boolean with rfl | rfl <;> simp [evaluate]

theorem evaluate_group [CommRing R] [Nontrivial R] [DecidableEq R]
    (execute : R) (boolean : execute = 0 ∨ execute = 1) (encode : α → R) (values : List α) :
    ((values.map (contribution execute)).map (evaluate encode)).prod =
      mask execute (values.map encode).prod := by
  rcases boolean with rfl | rfl <;> simp [evaluate, List.map_map, Function.comp_def]

theorem erase_contributions [One R] [DecidableEq R] (rows : List ρ)
    (execute : ρ → R) (values : ρ → List α) :
    (contributions rows execute values).filterMap (fun value => value) =
      (rows.filter fun row => decide (execute row = 1)).flatMap values := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    change ((values row).map (contribution (execute row)) ++ contributions rest execute values).filterMap
      (fun value => value) = _
    by_cases selected : execute row = 1
    · simp [contribution, selected, List.filterMap_append, ih]
    · simp [contribution, selected, List.filterMap_append, ih]

theorem flatMap_values (rows : List ρ) (value : ρ → α) :
    (rows.flatMap fun row => [value row]) = rows.map value := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]

theorem projected_states {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (binding : Binding trace) :
    ((active trace).initial :: (active trace).rows.map Row.finish).Perm
      ((active trace).terminal :: (active trace).rows.map Row.start) := by
  have matched := binding.states.filterMap (fun value => value)
  simpa only [List.filterMap_cons, id_eq, erase_contributions, flatMap_values,
    active] using matched

theorem projected_memory {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (binding : Binding trace) :
    ((active trace).initialMemory ++ (active trace).rows.flatMap Row.writes).Perm
      ((active trace).terminalMemory ++ (active trace).rows.flatMap Row.reads) := by
  have matched := binding.memory.filterMap (fun value => value)
  simpa only [List.filterMap_append, List.filterMap_map, Function.comp_def, id_eq,
    List.filterMap_some, erase_contributions, active] using matched

theorem projected_acceptance {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : AcceptedLayout trace) : Trace.Accepted (active trace) := by
  refine ⟨?_, ?_, projected_states accepted.binding, projected_memory accepted.binding⟩
  · intro row member
    exact accepted.constraints row (List.mem_of_mem_filter member)
  · intro row member
    exact of_decide_eq_true (List.mem_filter.mp member).2

theorem contributions_selected [One R] [DecidableEq R] (rows : List ρ)
    (execute : ρ → R) (values : ρ → List α) :
    (∀ row ∈ rows, execute row = 1) →
      contributions rows execute values = (rows.flatMap values).map some := by
  induction rows with
  | nil => intro _; rfl
  | cons row rest ih =>
    intro selected
    have head := selected row (List.mem_cons_self ..)
    have tail := ih (fun current member => selected current (List.mem_cons_of_mem _ member))
    change (values row).map (contribution (execute row)) ++ contributions rest execute values =
      ((values row) ++ rest.flatMap values).map some
    rw [tail, List.map_append]
    simp [head, contribution]

theorem binding_of_accepted {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : Trace.Accepted trace) : Binding trace := by
  refine ⟨fun row member => Or.inr (accepted.active row member), ?_, ?_⟩
  · rw [contributions_selected _ _ _ accepted.active, contributions_selected _ _ _ accepted.active]
    simpa only [flatMap_values, List.map_cons] using accepted.states.map some
  · rw [contributions_selected _ _ _ accepted.active, contributions_selected _ _ _ accepted.active]
    simpa only [List.map_append] using accepted.memory.map some

theorem insert_identities {a b c d : List α} (matched : (a ++ b).Perm (c ++ d)) (padding : List α) :
    (a ++ padding ++ b).Perm (c ++ padding ++ d) := by
  have left : (a ++ padding ++ b).Perm (padding ++ (a ++ b)) := by
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := a) (l₂ := padding)).append_right b
  have right : (c ++ padding ++ d).Perm (padding ++ (c ++ d)) := by
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := c) (l₂ := padding)).append_right d
  exact left.trans ((matched.append_left padding).trans right.symm)

theorem binding_cons_inactive {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (binding : Binding trace) (row : Row p Kind)
    (zero : row.assignment row.columns.execute = 0) :
    Binding { trace with rows := row :: trace.rows } := by
  refine ⟨?_, ?_, ?_⟩
  · intro current member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl zero
    · exact binding.selectors current member
  · change (some trace.initial :: contributions (row :: trace.rows) _ _).Perm
      (some trace.terminal :: contributions (row :: trace.rows) _ _)
    simp only [contributions, List.flatMap_cons, List.map_singleton, zero, contribution_zero, List.singleton_append]
    exact ((List.Perm.swap _ _ _).trans (List.Perm.cons none binding.states)).trans (List.Perm.swap _ _ _)
  · change (trace.initialMemory.map some ++ contributions (row :: trace.rows) _ _).Perm
      (trace.terminalMemory.map some ++ contributions (row :: trace.rows) _ _)
    simp only [contributions, List.flatMap_cons, Row.writes, Row.reads, List.map_map, Function.comp_def,
      zero, contribution_zero]
    simpa only [contributions, Row.writes, Row.reads, List.map_map, Function.comp_def, List.append_assoc] using
      insert_identities binding.memory (row.ports.toList.map fun _ => none)

theorem layout_of_accepted {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : Trace.Accepted trace) : AcceptedLayout trace :=
  ⟨accepted.constraints, binding_of_accepted accepted⟩

theorem layout_cons_inactive {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : AcceptedLayout trace) (row : Row p Kind)
    (zero : row.assignment row.columns.execute = 0)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom)) :
    AcceptedLayout { trace with rows := row :: trace.rows } := by
  refine ⟨?_, binding_cons_inactive accepted.binding row zero⟩
  intro current member
  rcases List.mem_cons.mp member with rfl | member
  · exact constraints
  · exact accepted.constraints current member

theorem active_idempotent {Kind : Type} [CircuitLayout Kind] [Fact p.Prime] (trace : Data p Kind) :
    active (active trace) = active trace := by
  simp [active, List.filter_filter]

theorem active_of_accepted {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} (accepted : Trace.Accepted trace) : active trace = trace := by
  have rows : (trace.rows.filter fun row => decide (row.assignment row.columns.execute = 1)) = trace.rows := by
    apply List.filter_eq_self.mpr
    intro row member
    exact decide_eq_true (accepted.active row member)
  simp [active, rows]

end Airbender.PaddingBoundary.Proofs
