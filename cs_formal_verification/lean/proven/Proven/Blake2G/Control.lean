module
public import Proven.Defs.Circuits.Blake2G.Control
public import Proven.Blake2G
public import Mathlib.Tactic.IntervalCases
public import Proven.CleanCore.Circuit.Operations
public import Proven.Defs.Circuits.Blake2G.Artifact
public import Proven.Defs.Circuits.Blake2G.Controller

@[expose] public section

namespace Airbender.Blake2G.Control.Proofs

private theorem lanes_bounded : ∀ m : Fin 8, ∀ k (h : k < 4), stateLanes[m][k] < 16 := by
  decide

private theorem schedule_bounded :
    ∀ r : Fin 10, ∀ k (h : k < 16), messageSchedule[r][k] < 16 := by
  decide

private theorem lanes_distinct : ∀ m : Fin 8, stateLanes[m].toList.Pairwise (· ≠ ·) := by
  decide

/-- Every row of `step`: a counter byte, then six word indices below 16. -/
private theorem step_row_bounded (input : Input) :
    (step input).row[0] < 256 ∧ ∀ j : Fin 6, (step input).row[j.val + 1] < 16 := by
  have register := input.register.isLt
  unfold step
  split
  · refine ⟨by simp [Output.row], fun j => ?_⟩
    fin_cases j <;> simp [Output.row]
  · refine ⟨?_, fun j => ?_⟩
    · simp only [Output.row, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
      split_ifs <;> omega
    fin_cases j <;> simp only [Output.row, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceAdd] <;> first
      | exact lanes_bounded _ _ (by decide)
      | exact schedule_bounded _ _ (by omega)

/-- All 512 modeled rows have canonical eight-bit outputs; lane bounds are
    checked separately below. -/
theorem controller_bounded : ∀ key : Fin 512, ∀ j : Fin 7, (controllerRows key)[j] < 256 := by
  intro key j
  have bounds :=
    step_row_bounded ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ key.val)⟩
  unfold controllerRows
  by_cases first : j.val = 0
  · simpa only [Fin.getElem_fin, first] using bounds.1
  · have lane := bounds.2 ⟨j.val - 1, by omega⟩
    simp only [Nat.sub_add_cancel (Nat.pos_of_ne_zero first)] at lane
    simp only [Fin.getElem_fin]
    omega

theorem controller_lanes : ∀ key : Fin 512, ∀ j : Fin 6, (controllerRows key)[j.val + 1] < 16 :=
  fun key => (step_row_bounded ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩,
    decide (256 ≤ key.val)⟩).2

private theorem active_rows_distinct (register : Fin 256) :
    (step ⟨register, true⟩).stateOffsets.toList.Pairwise (· ≠ ·) := by
  simp only [step, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact lanes_distinct _

/-- Every active modeled controller row selects four different state words. -/
theorem active_state_distinct (input : Input) (active : input.active = true) :
    (step input).stateOffsets.toList.Pairwise (· ≠ ·) := by
  rcases input with ⟨register, flag⟩
  cases flag
  · cases active
  · exact active_rows_distinct register

theorem controller_input (input : Input) : controllerRows input.key = (step input).row := by
  have original : (⟨⟨input.key.val % 256, Nat.mod_lt _ (by decide)⟩,
      decide (256 ≤ input.key.val)⟩ : Input) = input := by
    cases input with
    | mk register active =>
      cases active
      all_goals congr 1
      all_goals first
        | (apply Fin.ext; simp [Input.key, Nat.mod_eq_of_lt register.isLt])
        | simp [Input.key]
  exact congrArg (fun i => (step i).row) original

theorem state_offsets_bounded (input : Input) (i : Fin 4) : (step input).stateOffsets[i] < 16 := by
  have bound := controller_lanes input.key ⟨i.val, by omega⟩
  rw [controller_input] at bound
  fin_cases i <;> simpa [Output.row] using bound

theorem message_offsets_bounded (input : Input) (i : Fin 2) : (step input).messageOffsets[i] < 16 := by
  have bound := controller_lanes input.key ⟨i.val + 4, by omega⟩
  rw [controller_input] at bound
  fin_cases i <;> simpa [Output.row] using bound

theorem control_columns {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable controllerRows))) :
    ∃ key : Fin 512, w 3 + 256 * w 0 = (key.val : ZMod p) ∧
      ∀ j : Fin 7, w (#v[5, 7, 8, 9, 10, 11, 12][j] : Nat) = ((controllerRows key)[j] : ZMod p) := by
  have member := Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩
  obtain ⟨key, input, outputs⟩ := Airbender.Blake2G.Proofs.control_lookup hp member
    (by simp [Expression.eval, Verification.environment])
  refine ⟨key, ?_, ?_⟩
  · simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
      Verification.environment, add_comm, mul_comm] using input
  · intro j
    have equation := outputs j
    fin_cases j <;> simpa [importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment] using equation

private theorem output_eq_of_row {left right : Output}
    (row : left.row = right.row) (high : left.register.hi = right.register.hi) : left = right := by
  have column (j : Fin 7) := congrArg (fun (v : Vector Nat 7) => v[j]) row
  have lo : left.register.lo = right.register.lo := by simpa [Output.row] using column 0
  have lanes : left.stateOffsets = right.stateOffsets := by
    apply Vector.ext
    intro i hi
    have equation := column ⟨i + 1, by omega⟩
    interval_cases i <;> simpa [Output.row, Variables.stateOffsetColumns,
      Variables.messageOffsetColumns] using equation
  have message : left.messageOffsets = right.messageOffsets := by
    apply Vector.ext
    intro i hi
    have equation := column ⟨i + 5, by omega⟩
    interval_cases i <;> simpa [Output.row] using equation
  cases left with
  | mk leftRegister leftState leftMessage =>
    cases right with
    | mk rightRegister rightState rightMessage =>
      cases leftRegister
      cases rightRegister
      cases lo
      cases high
      cases lanes
      cases message
      rfl

/-- The actual imported controller lookup selects the complete modeled row.
    Canonical input decoding prevents execute/key aliasing in the field. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) :
    Properties.Soundness (circuitModel (p := p)).relation spec := by
  intro input output w relation
  obtain ⟨constraints, mapping⟩ := relation
  obtain ⟨key, keyEquation, columns⟩ := control_columns hp constraints
  have decoded : w 3 = (input.register.val : ZMod p) := by
    rw [mapping.inputRegister]
    exact (ZMod.natCast_zmod_val _).symm
  have encoded : (input.key.val : ZMod p) = (key.val : ZMod p) := by
    rw [decoded, mapping.execute] at keyEquation
    cases active : input.active <;> simpa [Input.key, active] using keyEquation
  have keyEqual : input.key = key := by
    apply Fin.ext
    have values := congrArg ZMod.val encoded
    rw [ZMod.val_natCast_of_lt (by have size := input.key.isLt; omega),
      ZMod.val_natCast_of_lt (by have size := key.isLt; omega)] at values
    exact values
  have naturalColumns (j : Fin 7) :
      (w (#v[5, 7, 8, 9, 10, 11, 12][j] : Nat)).val = (step input).row[j] := by
    rw [columns j, ZMod.val_natCast_of_lt (by have := controller_bounded key j; omega),
      ← keyEqual, controller_input]
  have outputRow : output.row = (step input).row := by
    apply Vector.ext
    intro i hi
    have equation := naturalColumns ⟨i, hi⟩
    rw [mapping.outputs]
    interval_cases i <;> simpa [Output.row] using equation
  have highZero : (step input).register.hi = 0 := by
    unfold step
    split_ifs <;> rfl
  apply output_eq_of_row outputRow
  rw [mapping.outputs, highZero]
  have enforced := (Airbender.Blake2G.Proofs.control_high_zero constraints).2
  simp [enforced]

end Airbender.Blake2G.Control.Proofs
