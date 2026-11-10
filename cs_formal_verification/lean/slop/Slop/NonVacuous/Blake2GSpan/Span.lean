module
public import Slop.NonVacuous.Blake2GSpan.Steps
public import Slop.NonVacuous.Basic
public import Human.Trace.Workers.Blake2G.RVCall
public import Human.Helpers.Delegation.Operations

@[expose] public section

/-! A complete reduced G span (56 rows) from an `RV.State`: the witness that the assumptions of the Blake2s G
    work-vector, boundary and window claims can be met. x10 = 0x400000 (sixteen state words), x11 = 0x400040
    (sixteen message words), x12 = 128 (reduced mode, call 0), RAM a byte pattern. Row `k` is the honest row
    (`Row.lean`) read from the memory after rows `0 … k-1` at invocation clock `1 + 4 k`; the rows are a recursion
    over `k`, and every fact is proven by induction from the one-row lemmas (`Block.lean`, `Steps.lean`). -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic Trace

local notation "P" => babyBearModulus

/-- The starting state: the two pointers and the reduced control word, RAM a byte pattern. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 0x400000 else if i = 11 then 0x400040 else if i = 12 then 128 else 0
  rom _ := 0
  mem address := BitVec.ofNat 8 (address.toNat * 37 + 11)

/-- The seed tokens read from `before`. -/
def seed : Memory := fun cell => cell.initialToken ((cell.readRV before).getD 0)

/-- The memory before row `k`. -/
def memAt : Nat → Memory
  | 0 => seed
  | k + 1 => runFinal (memAt k) ((memAt k).steps (1 + 4 * k))

/-- Row `k`, at invocation clock `1 + 4 k`. -/
def rowAt (k : Nat) : Delegation.Row P := (memAt k).row (1 + 4 * k)

/-- The run's steps of rows `0 … n-1`. -/
def stepsUpTo : Nat → List (Cell × MemoryToken P)
  | 0 => []
  | k + 1 => stepsUpTo k ++ (memAt k).steps (1 + 4 * k)

def rows (n : Nat) : List (Delegation.Row P) := (List.range n).map rowAt

theorem seed_inv : Inv seed 1 where
  address _ _ := rfl
  high _ _ := rfl
  time _ _ := by simp [seed, Cell.initialToken]
  words c _ := seed_bounded c _
  state := by decide +kernel
  message := by decide +kernel
  control := by decide +kernel

theorem inv_at (k : Nat) (small : k ≤ 56) : Inv (memAt k) (1 + 4 * k) := by
  induction k with
  | zero => exact seed_inv
  | succ k ih =>
    have next := next (ih (by omega)) (by omega) (by simp only [timestampBase]; omega)
    rwa [show 1 + 4 * k + 4 = 1 + 4 * (k + 1) by omega] at next

theorem final_at (n : Nat) : runFinal seed (stepsUpTo n) = memAt n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepsUpTo, runFinal_append, ih, memAt]

theorem edges_at (n : Nat) (small : n ≤ 56) :
    (rows n).flatMap Delegation.Row.memorySteps = runEdges seed (stepsUpTo n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rows, List.range_succ, List.map_append, List.flatMap_append, ← rows, ih (by omega), stepsUpTo,
      runEdges_append, final_at]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowAt]
    rw [edges (inv_at n (by omega))]

theorem inside (n : Nat) (small : n ≤ 56) : ∀ step ∈ stepsUpTo n, step.1 ∈ cells := by
  induction n with
  | zero => intro _ member; cases member
  | succ n ih =>
    intro step member
    rcases List.mem_append.mp member with earlier | current
    · exact ih (by omega) step earlier
    · have key : step.1 ∈ (memAt n).ports.toList := keys (memAt n) (1 + 4 * n) ▸ List.mem_map_of_mem current
      obtain ⟨j, h, same⟩ := List.mem_iff_getElem.mp key
      rw [← same, Vector.getElem_toList]
      exact ports_mem (inv_at n (by omega)) ⟨j, by simpa using h⟩

theorem row_mem {n : Nat} {row : Delegation.Row P} (member : row ∈ rows n) : ∃ k < n, row = rowAt k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

/-- The invocation clock of row `k`. -/
theorem invocation_at (k : Nat) (small : k ≤ 56) :
    decodeTimestamp (rowAt k).assignment (rowAt k).columns.invocation = ⟨1 + 4 * k, 0⟩ := by
  show (⟨(((1 + 4 * k : Nat) : ZMod P)).val, (((0 : Nat) : ZMod P)).val⟩ : Timestamp) = _
  rw [ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega), Nat.cast_zero, ZMod.val_zero]

theorem write_time_at (k : Nat) (small : k ≤ 56) : (rowAt k).writeTime = 1 + 4 * k + 2 := by
  show (((((1 + 4 * k : Nat) : ZMod P) + 2)).val + timestampBase * (((0 : Nat) : ZMod P)).val) = _
  rw [show ((1 + 4 * k : Nat) : ZMod P) + 2 = ((1 + 4 * k + 2 : Nat) : ZMod P) by push_cast; ring,
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega), Nat.cast_zero, ZMod.val_zero]
  omega

noncomputable def data : Delegation.MemoryData P where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := rows 56
  initial := cells.map seed
  terminal := cells.map (memAt 56)

theorem accepted : Delegation.MemoryAccepted data where
  constraints row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    have inv := inv_at k (by omega)
    exact holds ((memAt k).input (1 + 4 * k)) (valid inv (by omega) (by simp only [timestampBase]; omega)) rfl
  matching := by
    have run := run_matching (by decide +kernel : cells.Nodup) seed (inside 56 le_rfl)
    rw [final_at] at run
    simp only [Delegation.MemoryData.steps, data, edges_at 56 le_rfl]
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

theorem family : ∀ row ∈ data.rows, row.family = .blakeG := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem member
  rfl

theorem active : ∀ row ∈ data.rows, row.assignment Blake2G.Variables.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem member
  exact Nat.cast_one

theorem control_start : (Cell.register 12).readRV before = some (if true then 128 else 0) := by decide

theorem call_inputs : Blake2G.RVCallInputs data before cells true where
  memory := memory_inputs
  tables := rfl
  family := family
  active := active
  controlStart := control_start
  calls := by simp [data, rows, Blake2G.callCount]

theorem native_call_inputs : Blake2G.RVNativeCallInputs data before cells true where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family
  active := active
  controlStart := control_start
  calls := by simp [data, rows, Blake2G.callCount]

/-- The whole span is one window after an empty prefix: every row writes in `(0, 1000]`. -/
theorem window_inputs : Blake2G.RVWindowInputs data before cells true 0 1000 where
  memory := memory_inputs
  tables := rfl
  family := family
  active := active
  controlStart := control_start
  prefixComplete := by
    rw [Delegation.MemoryData.prefixRows, List.filter_eq_nil_iff.mpr]
    · rfl
    · intro row member
      obtain ⟨k, small, rfl⟩ := row_mem member
      rw [write_time_at k (by omega)]
      simp
  calls := by
    rw [Delegation.MemoryData.windowRows, List.filter_eq_self.mpr]
    · simp [data, rows, Blake2G.callCount]
    · intro row member
      obtain ⟨k, small, rfl⟩ := row_mem member
      rw [write_time_at k (by omega)]
      simp only [decide_eq_true_eq]
      omega

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide +kernel

end Airbender.NonVacuous.Blake2GSpan
