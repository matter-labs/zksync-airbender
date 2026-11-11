module
public import Slop.NonVacuous.Blake2GSpan.Steps
public import Slop.NonVacuous.HashCallers.Run
public import Human.Helpers.Delegation.Operations
public import Human.Helpers.Delegation.NativeWindows
public import Human.Circuits.Keccak.Tables.Controller

@[expose] public section

/-! A complete reduced G span (56 rows) from any start memory `m0` at any first invocation clock `t0 ≡ 1 (mod 4)`
    satisfying the span invariant (`Start`). Row `k` is the honest row (`Row.lean`) read from the memory after rows
    `0 … k-1` at invocation clock `t0 + 4 k`; the rows are a recursion over `k`, and every fact is proven by induction
    from the one-row lemmas (`Blake2GSpan/Block.lean`, `Blake2GSpan/Steps.lean`), as in `Blake2GSpan/Span.lean` (the
    seed at clock 1); the caller traces start later, after their first caller (and preparation) rows. -/

namespace Airbender.NonVacuous.HashCallers
open Arithmetic Trace NonVacuous.Blake2GSpan

local notation "P" => babyBearModulus

section
variable (m0 : Memory) (t0 : Nat)

/-- The memory before row `k`. -/
def memFrom : Nat → Memory
  | 0 => m0
  | k + 1 => runFinal (memFrom k) ((memFrom k).steps (t0 + 4 * k))

/-- Row `k`, at invocation clock `t0 + 4 k`. -/
def rowFrom (k : Nat) : Delegation.Row P := (memFrom m0 t0 k).row (t0 + 4 * k)

/-- The run's steps of row `k`. -/
def stepsFrom (k : Nat) : List (Cell × MemoryToken P) := (memFrom m0 t0 k).steps (t0 + 4 * k)

/-- The run's steps of the whole span. -/
def spanSteps : List (Cell × MemoryToken P) := (List.range 56).flatMap (stepsFrom m0 t0)

def rowsFrom (n : Nat) : List (Delegation.Row P) := (List.range n).map (rowFrom m0 t0)

/-- The span's worker pool over the modeled tables: its seeds are `m0` and its terminal tokens the memory after it. -/
noncomputable def workersFrom : Delegation.MemoryData P where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := rowsFrom m0 t0 56
  initial := cells.map m0
  terminal := cells.map (memFrom m0 t0 56)

end

/-- A span start: the invariant at a first invocation clock `≡ 1 (mod 4)`, with clock room for the 56 rows. -/
structure Start (m0 : Memory) (t0 : Nat) : Prop where
  inv : Inv m0 t0
  step : t0 % 4 = 1
  room : t0 + 4 * 56 < timestampBase

/-- The invariant holds at any later clock. -/
theorem inv_mono {mem : Memory} {t t' : Nat} (inv : Inv mem t) (later : t ≤ t') : Inv mem t' where
  address := inv.address
  high := inv.high
  time c member := Nat.le_trans (inv.time c member) later
  words := inv.words
  state := inv.state
  message := inv.message
  control := inv.control

variable {m0 : Memory} {t0 : Nat}

theorem inv_from (start : Start m0 t0) (k : Nat) (small : k ≤ 56) : Inv (memFrom m0 t0 k) (t0 + 4 * k) := by
  have room := start.room
  induction k with
  | zero => exact start.inv
  | succ k ih =>
    have next := next (ih (by omega)) (by have := start.step; omega) (by omega)
    rwa [show t0 + 4 * k + 4 = t0 + 4 * (k + 1) by omega] at next

/-- The rows' memory steps are the run's edges from `m0`, and the run ends at the memory after the span. -/
theorem blocks_from (start : Start m0 t0) :
    (rowsFrom m0 t0 56).flatMap Delegation.Row.memorySteps = runEdges m0 (spanSteps m0 t0) ∧
      runFinal m0 (spanSteps m0 t0) = memFrom m0 t0 56 := by
  have room := start.room
  rw [rowsFrom, List.flatMap_map]
  exact run_blocks (mem := memFrom m0 t0) 56 (fun k _ => rfl)
    (fun k small => edges (inv_from start k (by omega)))

theorem inside_from (start : Start m0 t0) : ∀ step ∈ spanSteps m0 t0, step.1 ∈ cells := by
  intro step member
  obtain ⟨k, present, current⟩ := List.mem_flatMap.mp member
  have small := List.mem_range.mp present
  have key : step.1 ∈ (memFrom m0 t0 k).ports.toList :=
    keys (memFrom m0 t0 k) (t0 + 4 * k) ▸ List.mem_map_of_mem current
  obtain ⟨j, h, same⟩ := List.mem_iff_getElem.mp key
  rw [← same, Vector.getElem_toList]
  exact ports_mem (inv_from start k (by omega)) ⟨j, by simpa using h⟩

theorem row_mem_from {n : Nat} {row : Delegation.Row P} (member : row ∈ rowsFrom m0 t0 n) :
    ∃ k < n, row = rowFrom m0 t0 k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

/-- The raw invocation clock of row `k`. -/
theorem invocation_raw (m0 : Memory) (t0 k : Nat) :
    rawPair (rowFrom m0 t0 k).assignment (rowFrom m0 t0 k).columns.invocation =
      (((t0 + 4 * k : Nat) : ZMod P), ((0 : Nat) : ZMod P)) := rfl

/-- The invocation clock of row `k`. -/
theorem invocation_from (start : Start m0 t0) (k : Nat) (small : k ≤ 56) :
    decodeTimestamp (rowFrom m0 t0 k).assignment (rowFrom m0 t0 k).columns.invocation = ⟨t0 + 4 * k, 0⟩ := by
  have room := start.room
  show (⟨(((t0 + 4 * k : Nat) : ZMod P)).val, (((0 : Nat) : ZMod P)).val⟩ : Timestamp) = _
  rw [ZMod.val_natCast_of_lt (by simp only [timestampBase] at room; unfold babyBearModulus; omega), Nat.cast_zero,
    ZMod.val_zero]

theorem write_time_from (start : Start m0 t0) (k : Nat) (small : k ≤ 56) :
    (rowFrom m0 t0 k).writeTime = t0 + 4 * k + 2 := by
  have room := start.room
  show (((((t0 + 4 * k : Nat) : ZMod P) + 2)).val + timestampBase * (((0 : Nat) : ZMod P)).val) = _
  rw [show ((t0 + 4 * k : Nat) : ZMod P) + 2 = ((t0 + 4 * k + 2 : Nat) : ZMod P) by push_cast; ring,
    ZMod.val_natCast_of_lt (by simp only [timestampBase] at room; unfold babyBearModulus; omega), Nat.cast_zero,
    ZMod.val_zero]
  omega

theorem accepted_from (start : Start m0 t0) : Delegation.MemoryAccepted (workersFrom m0 t0) where
  constraints row member := by
    obtain ⟨k, small, rfl⟩ := row_mem_from member
    have inv := inv_from start k (by omega)
    have room := start.room
    exact holds ((memFrom m0 t0 k).input (t0 + 4 * k))
      (valid inv (by have := start.step; omega) (by omega)) rfl
  matching := by
    have run := run_matching (by decide +kernel : cells.Nodup) m0 (inside_from start)
    obtain ⟨edges, final⟩ := blocks_from start
    rw [final] at run
    simp only [Delegation.MemoryData.steps, workersFrom, edges]
    exact run

theorem family_from : ∀ row ∈ (workersFrom m0 t0).rows, row.family = .blakeG := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem_from member
  rfl

theorem active_from : ∀ row ∈ (workersFrom m0 t0).rows, row.assignment Blake2G.Variables.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem_from member
  exact Nat.cast_one

theorem execute_from : ∀ row ∈ (workersFrom m0 t0).rows, row.assignment row.columns.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem_from member
  exact Nat.cast_one

theorem calls_from : (workersFrom m0 t0).rows.length = 56 := by simp [workersFrom, rowsFrom]

theorem clock_room_from (start : Start m0 t0) : ∀ row ∈ (workersFrom m0 t0).rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase := by
  intro row member
  obtain ⟨k, small, rfl⟩ := row_mem_from member
  have room := start.room
  rw [invocation_from start k (by omega)]
  show t0 + 4 * k + 2 < timestampBase
  omega

theorem invocation_high_from (start : Start m0 t0) : ∀ row ∈ (workersFrom m0 t0).rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase := by
  intro row member
  obtain ⟨k, small, rfl⟩ := row_mem_from member
  rw [invocation_from start k (by omega)]
  show 0 < timestampBase
  decide

/-- No row writes at or before a cut below the first write. -/
theorem prefix_from (start : Start m0 t0) {lower : Nat} (below : lower < t0 + 2) :
    (workersFrom m0 t0).prefixRows lower = [] := by
  rw [Delegation.MemoryData.prefixRows, List.filter_eq_nil_iff]
  intro row member
  obtain ⟨k, small, rfl⟩ := row_mem_from member
  rw [write_time_from start k (by omega)]
  simp only [decide_eq_true_eq]
  omega

/-- Every row writes inside a window around the span. -/
theorem window_from (start : Start m0 t0) {lower upper : Nat} (below : lower < t0 + 2)
    (above : t0 + 4 * 55 + 2 ≤ upper) : (workersFrom m0 t0).windowRows lower upper = (workersFrom m0 t0).rows := by
  rw [Delegation.MemoryData.windowRows, List.filter_eq_self]
  intro row member
  obtain ⟨k, small, rfl⟩ := row_mem_from member
  rw [write_time_from start k (by omega)]
  simp only [decide_eq_true_eq]
  omega

end Airbender.NonVacuous.HashCallers
