module
public import Slop.NonVacuous.Blake2RoundSpan.Steps
public import Slop.NonVacuous.Blake2RoundSpan.Row
public import Human.Trace.Workers.Blake2Round.RVCall
public import Human.Helpers.Delegation.Operations

@[expose] public section

/-! A complete ten-round extended-control Blake2s span (plain mode, flags 0) from an `RV.State`: the witness that the
    assumptions of the round compression, boundary and window claims can be met. x10 = 0x400000 (8 state and 16
    extended words), x11 = 0x400080 (16 message words), x12 = 0x80000 (round bit 0, no control flags), RAM a byte
    pattern. Row `k` is the honest round-`k` row (`Row.lean`) read from the memory after rows `0 … k-1` at
    invocation clock `1 + 4 k`; the rows are a recursion over `k`, and every fact is proven by induction from the
    one-row lemmas (`Block.lean`, `Ports.lean`, `Steps.lean`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic Trace Blake2GSpan

local notation "P" => babyBearModulus

/-- The starting state: the two pointers and the first round's control word, RAM a byte pattern. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 0x400000 else if i = 11 then 0x400080 else if i = 12 then 0x80000 else 0
  rom _ := 0
  mem address := BitVec.ofNat 8 (address.toNat * 37 + 11)

/-- The seed tokens read from `before`. -/
def seed : Memory := fun cell => cell.initialToken ((cell.readRV before).getD 0)

/-- The round of span position `k`. -/
def roundOf (k : Nat) : Fin 10 := ⟨k % 10, Nat.mod_lt _ (by decide)⟩

theorem roundOf_eq {k : Nat} (hk : k < 10) : roundOf k = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)

/-- The memory before row `k`. -/
def memAt : Nat → Memory
  | 0 => seed
  | k + 1 => runFinal (memAt k) (stepsAt (memAt k) (1 + 4 * k) (roundOf k))

/-- Row `k`, at invocation clock `1 + 4 k`. -/
def rowAt (k : Nat) : Delegation.Row P := rowAt' (memAt k) (1 + 4 * k) (roundOf k)

/-- The run's steps of rows `0 … n-1`. -/
def stepsUpTo : Nat → List (Cell × MemoryToken P)
  | 0 => []
  | k + 1 => stepsUpTo k ++ stepsAt (memAt k) (1 + 4 * k) (roundOf k)

def rows (n : Nat) : List (Delegation.Row P) := (List.range n).map rowAt

theorem seed_inv : Inv seed 1 0 where
  address _ _ := rfl
  high _ _ := rfl
  time _ _ := by simp [seed, Cell.initialToken]
  words c _ := seed_bounded c _
  state := by decide +kernel
  message := by decide +kernel
  control := by decide +kernel

theorem inv_at (k : Nat) (small : k ≤ 10) : Inv (memAt k) (1 + 4 * k) k := by
  induction k with
  | zero => exact seed_inv
  | succ k ih =>
    have next := next (ih (by omega)) (by omega : k < 10) (by omega) (by simp only [timestampBase]; omega)
    rw [show 1 + 4 * k + 4 = 1 + 4 * (k + 1) by omega, ← roundOf_eq (by omega : k < 10)] at next
    exact next

theorem final_at (n : Nat) : runFinal seed (stepsUpTo n) = memAt n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepsUpTo, runFinal_append, ih, memAt]

theorem edges_at (n : Nat) (small : n ≤ 10) :
    (rows n).flatMap Delegation.Row.memorySteps = runEdges seed (stepsUpTo n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rows, List.range_succ, List.map_append, List.flatMap_append, ← rows, ih (by omega), stepsUpTo,
      runEdges_append, final_at]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowAt]
    rw [roundOf_eq (by omega : n < 10), edges (inv_at n (by omega)) (by omega)]

theorem inside (n : Nat) : ∀ step ∈ stepsUpTo n, step.1 ∈ cells := by
  induction n with
  | zero => intro _ member; cases member
  | succ n ih =>
    intro step member
    rcases List.mem_append.mp member with earlier | current
    · exact ih step earlier
    · rw [← keys (memAt n) (1 + 4 * n) (roundOf n)]
      exact List.mem_map_of_mem current

theorem row_mem {n : Nat} {row : Delegation.Row P} (member : row ∈ rows n) : ∃ k < n, row = rowAt k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

/-- The invocation clock of row `k`. -/
theorem invocation_at (k : Nat) (small : k ≤ 10) :
    decodeTimestamp (rowAt k).assignment (rowAt k).columns.invocation = ⟨1 + 4 * k, 0⟩ := by
  show (⟨(((1 + 4 * k : Nat) : ZMod P)).val, (((0 : Nat) : ZMod P)).val⟩ : Timestamp) = _
  rw [ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega), Nat.cast_zero, ZMod.val_zero]

theorem write_time_at (k : Nat) (small : k ≤ 10) : (rowAt k).writeTime = 1 + 4 * k + 2 := by
  show (((((1 + 4 * k : Nat) : ZMod P) + 2)).val + timestampBase * (((0 : Nat) : ZMod P)).val) = _
  rw [show ((1 + 4 * k : Nat) : ZMod P) + 2 = ((1 + 4 * k + 2 : Nat) : ZMod P) by push_cast; ring,
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega), Nat.cast_zero, ZMod.val_zero]
  omega

noncomputable def data : Delegation.MemoryData P where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := rows 10
  initial := cells.map seed
  terminal := cells.map (memAt 10)

theorem accepted : Delegation.MemoryAccepted data where
  constraints row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    have valid := valid (inv_at k (by omega)) small (by omega) (by simp only [timestampBase]; omega)
    rw [← roundOf_eq small] at valid
    exact holds (p := P) rfl valid
  matching := by
    have run := run_matching cells_nodup seed (inside 10)
    rw [final_at] at run
    simp only [Delegation.MemoryData.steps, data, edges_at 10 le_rfl]
    exact run

theorem readable : ∀ cell ∈ cells, (cell.readRV before).isSome := by decide +kernel

theorem memory_inputs : Delegation.RVMemoryInputs data before cells where
  initialization := initial_image readable
  distinct := by decide +kernel
  clockRoom row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    rw [invocation_at k (by omega)]
    simp only [timestampBase]
    omega
  invocationHigh row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    rw [invocation_at k (by omega)]
    show 0 < timestampBase
    decide

theorem family : ∀ row ∈ data.rows, row.family = .blakeRound := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem member
  rfl

theorem control_start : (Cell.register 12).readRV before = some (BitVec.ofNat 32 ((8 + (0 : Fin 8).val) * 65536)) := by
  decide +kernel

theorem calls : data.rows.length = if (0 : Fin 8).val % 2 = 1 then 7 else 10 := by simp [data, rows]

theorem call_inputs : Blake2Round.RVCallInputs data before cells 0 where
  memory := memory_inputs
  tables := rfl
  family := family
  controlStart := control_start
  calls := calls

theorem native_call_inputs : Blake2Round.RVNativeCallInputs data before cells 0 where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family
  controlStart := control_start
  calls := calls

/-- The whole span is the window after an empty prefix: every row writes in `(0, 1000]`. -/
theorem window_inputs : Blake2Round.RVWindowInputs data before cells 0 0 1000 where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family
  controlStart := control_start
  prefixEmpty := by
    rw [Delegation.MemoryData.prefixRows, List.filter_eq_nil_iff]
    intro row member
    obtain ⟨k, small, rfl⟩ := row_mem member
    rw [write_time_at k (by omega)]
    simp
  roundsBound := by simp [data, rows]
  calls := by
    rw [Delegation.MemoryData.windowRows, List.filter_eq_self.mpr]
    · simp [data, rows]
    · intro row member
      obtain ⟨k, small, rfl⟩ := row_mem member
      rw [write_time_at k (by omega)]
      simp only [decide_eq_true_eq]
      omega

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by
  simp only [cells, List.mem_map, List.mem_range]
  rintro _ ⟨j, hj, rfl⟩
  unfold cellAt
  split_ifs <;> simp only [Cell.Aligned, ramCell, stateBase, messageBase, Word.value, limbBase,
    BitVec.toNat_ofNat] <;> omega

end Airbender.NonVacuous.Blake2RoundSpan
