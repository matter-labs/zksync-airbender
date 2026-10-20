import Human.Circuits.Blake2G.Control
import Slop.Blake2G
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2G.Control.Proofs

set_option maxRecDepth 8192 in
/-- All 512 modeled rows have canonical eight-bit outputs; lane bounds are
    checked separately below. This finite calculation is kernel checked. -/
theorem controller_bounded : ∀ key : Fin 512, ∀ j : Fin 7, (controllerRows key)[j] < 256 := by
  decide

set_option maxRecDepth 8192 in
theorem controller_lanes : ∀ key : Fin 512, ∀ j : Fin 6, (controllerRows key)[j.val + 1] < 16 := by
  decide

set_option maxRecDepth 8192 in
private theorem active_rows_distinct : ∀ register : Fin 256,
    (step ⟨register, true⟩).stateOffsets.toList.Pairwise (· ≠ ·) := by
  decide

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
        | (simp [Input.key]; try omega)
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
