module
public import Human.Helpers.Context.Model
public import Human.Helpers.Memory.InitialImage

@[expose] public section

/-! One-row traces for the non-vacuity witnesses of the family trace claims: tokens of a cell, and `Accepted` from
    the row's own facts. -/

namespace Airbender.NonVacuous
open Trace

/-- The token of `cell` at clock `time` (high clock limb 0) holding the word with limbs `lo`, `hi`. -/
def cellToken {p : Nat} (cell : Cell) (time lo hi : Nat) : MemoryToken p :=
  ⟨cell.addressCode, (time, 0), Nat.pair lo hi⟩

/-- A trace of one row is accepted when the row satisfies its constraints, is active, runs from the trace's initial
    state to its terminal one, and its memory matching holds. -/
theorem accepted_of_row {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] {trace : Data p Kind}
    {row : Row p Kind} (rows : trace.rows = [row])
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints trace.rom))
    (active : row.assignment row.columns.execute = 1)
    (start : row.start = trace.initial) (terminal : trace.terminal = row.finish)
    (memory : (trace.initialMemory ++ row.writes).Perm (trace.terminalMemory ++ row.reads)) : Accepted trace where
  constraints current member := by
    rw [rows, List.mem_singleton] at member
    subst member
    exact constraints
  active current member := by
    rw [rows, List.mem_singleton] at member
    subst member
    exact active
  states := by
    simp only [rows, List.map_cons, List.map_nil, start, terminal]
    exact List.Perm.swap _ _ []
  memory := by
    simpa only [rows, List.flatMap_cons, List.flatMap_nil, List.append_nil] using memory

end Airbender.NonVacuous
