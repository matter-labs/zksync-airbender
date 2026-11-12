module
public import Slop.NonVacuous.Blake2RoundSpan.Steps
public import Slop.NonVacuous.Blake2RoundSpan.Row
public import Slop.NonVacuous.SequentialBlocks
public import Human.Helpers.Delegation.NativeWindows
public import Human.Helpers.Delegation.Operations
public import Human.Circuits.Keccak.Tables.Controller

@[expose] public section

/-! A complete ten-round extended-control Blake2s span (flags 0) from any start memory `m0` at any first invocation
    clock `t0 ≡ 1 (mod 4)` satisfying the span invariant before round 0 (`Start`). Row `k` is the honest round-`k` row
    (`Block.lean`) read from the memory after rows `0 … k-1` at invocation clock `t0 + 4 k`; the rows are a recursion
    over `k`, and every fact is proven by induction from the one-row lemmas (`Steps.lean`), as `Blake2GSpan/From.lean`
    for the G span. The pilot witness (`Span.lean`) is the span from the seed at clock 1; the caller trace starts
    later, after its preparation row. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Trace Blake2GSpan

local notation "P" => babyBearModulus

/-- The round of span position `k`. -/
def roundOf (k : Nat) : Fin 10 := ⟨k % 10, Nat.mod_lt _ (by decide)⟩

theorem roundOf_eq {k : Nat} (hk : k < 10) : roundOf k = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)

section
variable (m0 : Memory) (t0 : Nat)

/-- The memory before row `k`. -/
def memFrom : Nat → Memory
  | 0 => m0
  | k + 1 => runFinal (memFrom k) (stepsAt (memFrom k) (t0 + 4 * k) (roundOf k))

/-- Row `k`, at invocation clock `t0 + 4 k`. -/
def rowFrom (k : Nat) : Delegation.Row P := rowAt' (memFrom m0 t0 k) (t0 + 4 * k) (roundOf k)

/-- The run's steps of row `k`. -/
def stepsFrom (k : Nat) : List (Cell × MemoryToken P) := stepsAt (memFrom m0 t0 k) (t0 + 4 * k) (roundOf k)

/-- The run's steps of the whole span. -/
def spanSteps : List (Cell × MemoryToken P) := (List.range 10).flatMap (stepsFrom m0 t0)

def rowsFrom (n : Nat) : List (Delegation.Row P) := (List.range n).map (rowFrom m0 t0)

/-- The span's worker pool over the modeled tables: its seeds are `m0` and its terminal tokens the memory after it. -/
noncomputable def workersFrom : Delegation.MemoryData P where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := rowsFrom m0 t0 10
  initial := cells.map m0
  terminal := cells.map (memFrom m0 t0 10)

end

/-- A span start: the invariant before round 0 at a first invocation clock `≡ 1 (mod 4)`, with clock room for the
    ten rows. -/
structure Start (m0 : Memory) (t0 : Nat) : Prop where
  inv : Inv m0 t0 0
  step : t0 % 4 = 1
  room : t0 + 4 * 10 < timestampBase

/-- The invariant holds at any later clock. -/
theorem inv_mono {mem : Memory} {t t' k : Nat} (inv : Inv mem t k) (later : t ≤ t') : Inv mem t' k where
  address := inv.address
  high := inv.high
  time c member := Nat.le_trans (inv.time c member) later
  words := inv.words
  state := inv.state
  message := inv.message
  control := inv.control

/-- The invariant survives a new x12 token: at x12's address, with a low clock and the round's control word. -/
theorem inv_control {mem : Memory} {t k : Nat} (inv : Inv mem t k) {token : MemoryToken P}
    (address : token.address = (Cell.register 12).addressCode) (high : token.time.2 = 0) (time : token.time.1.val ≤ t)
    (control : token.word = controlWord k) : Inv (Function.update mem (.register 12) token) t k := by
  have bounded : token.word.Bounded := by
    rw [control]
    refine ⟨by simp [controlWord, limbBase], ?_⟩
    simp only [controlWord, limbBase]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  have other {c : Cell} (h : c ≠ .register 12) : Function.update mem (.register 12) token c = mem c :=
    Function.update_of_ne h ..
  refine ⟨fun c member => ?_, fun c member => ?_, fun c member => ?_, fun c member => ?_, ?_, ?_, ?_⟩
  · by_cases same : c = .register 12
    · subst same; rw [Function.update_self]; exact address
    · rw [other same]; exact inv.address c member
  · by_cases same : c = .register 12
    · subst same; rw [Function.update_self]; exact high
    · rw [other same]; exact inv.high c member
  · by_cases same : c = .register 12
    · subst same; rw [Function.update_self]; exact time
    · rw [other same]; exact inv.time c member
  · by_cases same : c = .register 12
    · subst same; rw [Function.update_self]; exact bounded
    · rw [other same]; exact inv.words c member
  · rw [other (by decide)]; exact inv.state
  · rw [other (by decide)]; exact inv.message
  · rw [Function.update_self]; exact control

variable {m0 : Memory} {t0 : Nat}

theorem inv_from (start : Start m0 t0) (k : Nat) (small : k ≤ 10) : Inv (memFrom m0 t0 k) (t0 + 4 * k) k := by
  have room := start.room
  induction k with
  | zero => exact start.inv
  | succ k ih =>
    have next := next (ih (by omega)) (by omega : k < 10) (by have := start.step; omega) (by omega)
    rw [show t0 + 4 * k + 4 = t0 + 4 * (k + 1) by omega, ← roundOf_eq (by omega : k < 10)] at next
    exact next

/-- The rows' memory steps are the run's edges from `m0`, and the run ends at the memory after the span. -/
theorem blocks_from (start : Start m0 t0) :
    (rowsFrom m0 t0 10).flatMap Delegation.Row.memorySteps = runEdges m0 (spanSteps m0 t0) ∧
      runFinal m0 (spanSteps m0 t0) = memFrom m0 t0 10 := by
  rw [rowsFrom, List.flatMap_map]
  refine run_blocks (mem := memFrom m0 t0) 10 (fun k _ => rfl) (fun k small => ?_)
  show (rowAt' (memFrom m0 t0 k) (t0 + 4 * k) (roundOf k)).memorySteps =
    runEdges (memFrom m0 t0 k) (stepsAt (memFrom m0 t0 k) (t0 + 4 * k) (roundOf k))
  rw [roundOf_eq small]
  exact edges (inv_from start k (by omega)) small

theorem inside_from : ∀ step ∈ spanSteps m0 t0, step.1 ∈ cells := by
  intro step member
  obtain ⟨k, -, current⟩ := List.mem_flatMap.mp member
  rw [← keys (memFrom m0 t0 k) (t0 + 4 * k) (roundOf k)]
  exact List.mem_map_of_mem current

theorem row_mem_from {n : Nat} {row : Delegation.Row P} (member : row ∈ rowsFrom m0 t0 n) :
    ∃ k < n, row = rowFrom m0 t0 k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

/-- The raw invocation clock of row `k`. -/
theorem invocation_raw (m0 : Memory) (t0 k : Nat) :
    rawPair (rowFrom m0 t0 k).assignment (rowFrom m0 t0 k).columns.invocation =
      (((t0 + 4 * k : Nat) : ZMod P), ((0 : Nat) : ZMod P)) := rfl

/-- The invocation clock of row `k`. -/
theorem invocation_from (start : Start m0 t0) (k : Nat) (small : k ≤ 10) :
    decodeTimestamp (rowFrom m0 t0 k).assignment (rowFrom m0 t0 k).columns.invocation = ⟨t0 + 4 * k, 0⟩ := by
  have room := start.room
  show (⟨(((t0 + 4 * k : Nat) : ZMod P)).val, (((0 : Nat) : ZMod P)).val⟩ : Timestamp) = _
  rw [ZMod.val_natCast_of_lt (by simp only [timestampBase] at room; unfold babyBearModulus; omega), Nat.cast_zero,
    ZMod.val_zero]

theorem write_time_from (start : Start m0 t0) (k : Nat) (small : k ≤ 10) :
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
    have room := start.room
    have valid := valid (inv_from start k (by omega)) small (by have := start.step; omega) (by omega)
    rw [← roundOf_eq small] at valid
    exact holds (p := P) rfl valid
  matching := by
    have run := run_matching cells_nodup m0 (inside_from (m0 := m0) (t0 := t0))
    obtain ⟨edges, final⟩ := blocks_from start
    rw [final] at run
    simp only [Delegation.MemoryData.steps, workersFrom, edges]
    exact run

theorem family_from : ∀ row ∈ (workersFrom m0 t0).rows, row.family = .blakeRound := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem_from member
  rfl

theorem execute_from : ∀ row ∈ (workersFrom m0 t0).rows, row.assignment row.columns.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem_from member
  exact Nat.cast_one

theorem calls_from : (workersFrom m0 t0).rows.length = 10 := by simp [workersFrom, rowsFrom]

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
    (above : t0 + 4 * 9 + 2 ≤ upper) : (workersFrom m0 t0).windowRows lower upper = (workersFrom m0 t0).rows := by
  rw [Delegation.MemoryData.windowRows, List.filter_eq_self]
  intro row member
  obtain ⟨k, small, rfl⟩ := row_mem_from member
  rw [write_time_from start k (by omega)]
  simp only [decide_eq_true_eq]
  omega

end Airbender.NonVacuous.Blake2RoundSpan
