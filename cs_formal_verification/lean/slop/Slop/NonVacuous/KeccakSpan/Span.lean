module
public import Slop.NonVacuous.KeccakSpan.Next
public import Slop.NonVacuous.Basic
public import Human.Trace.Workers.Keccak.RVCall
public import Human.Helpers.Delegation.Operations

@[expose] public section

/-! A complete special5 request (649 Keccak calls) from an `RV.State`: the witness that the assumptions of the
    Keccak permutation, boundary and window claims can be met. x10 = 0 (the first control word), x11 = 0x400000
    (the 31 lanes: 25 state lanes and 6 scratch lanes), RAM zero. Call `k` is the honest row (`Row.lean`) read
    from the memory after calls `0 … k-1` at invocation clock `1 + 4 k`, with the scheduled control word; the
    rows are a recursion over `k`, and every fact is proven by induction from the one-call lemmas (`Block.lean`,
    `Steps.lean`, `Next.lean`). -/

namespace Airbender.NonVacuous.KeccakSpan
open Arithmetic Trace

local notation "P" => babyBearModulus

/-- The starting state: control word 0 in x10, the state pointer in x11, RAM zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 11 then 0x400000 else 0
  rom _ := 0
  mem _ := 0

/-- The seed tokens read from `before`. -/
def seed : Memory := fun cell => cell.initialToken ((cell.readRV before).getD 0)

/-- The memory before call `k`. -/
def memAt : Nat → Memory
  | 0 => seed
  | k + 1 => runFinal (memAt k) ((memAt k).steps k (1 + 4 * k))

/-- Call `k`, at invocation clock `1 + 4 k`. -/
def rowAt (k : Nat) : Delegation.Row P := (memAt k).row k (1 + 4 * k)

/-- The run's steps of calls `0 … n-1`. -/
def stepsUpTo : Nat → List (Cell × MemoryToken P)
  | 0 => []
  | k + 1 => stepsUpTo k ++ (memAt k).steps k (1 + 4 * k)

/-- The first `n` calls (irreducible: elaboration never evaluates the 649-element list). -/
@[irreducible] def rows (n : Nat) : List (Delegation.Row P) := (List.range n).map rowAt

theorem seed_inv : Inv seed 0 where
  address _ _ := rfl
  high _ _ := rfl
  time _ _ := by simp [seed, Cell.initialToken]
  words c _ := seed_bounded c _
  pointer := by decide +kernel
  control := by decide +kernel

theorem inv_at (k : Nat) (small : k ≤ 649) : Inv (memAt k) k := by
  induction k with
  | zero => exact seed_inv
  | succ k ih => exact next (ih (by omega)) (by omega)

theorem final_at (n : Nat) : runFinal seed (stepsUpTo n) = memAt n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepsUpTo, runFinal_append, ih, memAt]

theorem edges_at (n : Nat) (small : n ≤ 649) :
    (rows n).flatMap Delegation.Row.memorySteps = runEdges seed (stepsUpTo n) := by
  induction n with
  | zero => simp only [rows, List.range_zero, List.map_nil, List.flatMap_nil, stepsUpTo, runEdges]
  | succ n ih =>
    rw [rows, List.range_succ, List.map_append, List.flatMap_append, ← rows, ih (by omega), stepsUpTo,
      runEdges_append, final_at]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowAt]
    rw [edges (inv_at n (by omega)) (by omega)]

theorem inside (n : Nat) : ∀ step ∈ stepsUpTo n, step.1 ∈ cells := by
  induction n with
  | zero => intro _ member; cases member
  | succ n ih =>
    intro step member
    rcases List.mem_append.mp member with earlier | current
    · exact ih step earlier
    · have key : step.1 ∈ (List.range 14).map (portCell n) :=
        keys (memAt n) n (1 + 4 * n) ▸ List.mem_map_of_mem current
      obtain ⟨m, -, same⟩ := List.mem_map.mp key
      rw [← same]
      exact portCell_mem n m

theorem row_mem {n : Nat} {row : Delegation.Row P} (member : row ∈ rows n) : ∃ k < n, row = rowAt k := by
  rw [rows] at member
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

/-- The invocation clock of call `k`. -/
theorem invocation_at (k : Nat) (small : k ≤ 649) :
    decodeTimestamp (rowAt k).assignment (rowAt k).columns.invocation = ⟨1 + 4 * k, 0⟩ := by
  show (⟨(((1 + 4 * k : Nat) : ZMod P)).val, (((0 : Nat) : ZMod P)).val⟩ : Timestamp) = _
  rw [ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega), Nat.cast_zero, ZMod.val_zero]

theorem write_time_at (k : Nat) (small : k ≤ 649) : (rowAt k).writeTime = 1 + 4 * k + 2 := by
  show (((((1 + 4 * k : Nat) : ZMod P) + 2)).val + timestampBase * (((0 : Nat) : ZMod P)).val) = _
  rw [show ((1 + 4 * k : Nat) : ZMod P) + 2 = ((1 + 4 * k + 2 : Nat) : ZMod P) by push_cast; ring,
    ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega), Nat.cast_zero, ZMod.val_zero]
  omega

noncomputable def data : Delegation.MemoryData P where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := rows 649
  initial := cells.map seed
  terminal := cells.map (memAt 649)

theorem accepted : Delegation.MemoryAccepted data where
  constraints row member := by
    obtain ⟨k, small, rfl⟩ := row_mem (n := 649) member
    exact holds ((memAt k).input k (1 + 4 * k)) (valid (inv_at k (by omega)) small) rfl
  matching := by
    have run := run_matching (by decide +kernel : cells.Nodup) seed (inside 649)
    rw [final_at] at run
    simp only [Delegation.MemoryData.steps, data, edges_at 649 le_rfl]
    exact run

theorem readable : ∀ cell ∈ cells, (cell.readRV before).isSome := by decide +kernel

theorem memory_inputs : Delegation.RVMemoryInputs data before cells where
  initialization := initial_image readable
  distinct := by decide +kernel
  clockRoom row member := by
    obtain ⟨k, small, rfl⟩ := row_mem (n := 649) member
    rw [invocation_at k (by omega)]
    simp only [timestampBase]
    omega
  invocationHigh row member := by
    obtain ⟨k, small, rfl⟩ := row_mem (n := 649) member
    rw [invocation_at k (by omega)]
    show 0 < timestampBase
    decide

theorem family : ∀ row ∈ data.rows, row.family = .keccak := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem (n := 649) member
  rfl

theorem active : ∀ row ∈ data.rows, row.assignment Keccak.Variables.execute = 1 := by
  intro row member
  obtain ⟨k, -, rfl⟩ := row_mem (n := 649) member
  exact Nat.cast_one

theorem control_start : (Cell.register 10).readRV before = some 0 := by decide

theorem call_count : data.rows.length = 649 := by simp [data, rows]

theorem call_inputs : Keccak.RVCallInputs data before cells where
  memory := memory_inputs
  controlCell := by decide
  controlStart := control_start
  family := family
  active := active
  calls := call_count

theorem native_call_inputs : Keccak.RVNativeCallInputs data before cells where
  memory := boundary_inputs memory_inputs
  controlStart := control_start
  family := family
  active := active
  calls := call_count

/-- The whole span is one window after an empty prefix: every call writes in `(0, 4000]`. -/
theorem window_inputs : Keccak.RVWindowInputs data before cells 0 4000 where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family
  active := active
  controlStart := control_start
  prefixEmpty := by
    rw [Delegation.MemoryData.prefixRows, List.filter_eq_nil_iff]
    intro row member
    obtain ⟨k, small, rfl⟩ := row_mem (n := 649) member
    rw [write_time_at k (by omega)]
    simp
  calls := by
    rw [Delegation.MemoryData.windowRows, List.filter_eq_self.mpr]
    · exact call_count
    · intro row member
      obtain ⟨k, small, rfl⟩ := row_mem (n := 649) member
      rw [write_time_at k (by omega)]
      simp only [decide_eq_true_eq]
      omega

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide +kernel

end Airbender.NonVacuous.KeccakSpan
