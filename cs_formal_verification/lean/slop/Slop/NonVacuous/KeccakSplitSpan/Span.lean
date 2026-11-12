module
public import Slop.NonVacuous.KeccakSplitSpan.Calls
public import Human.Trace.Workers.KeccakSplit.RVInputs
public import Slop.NonVacuous.Basic
public import Slop.NonVacuous.SequentialBlocks

@[expose] public section

/-! A complete split Keccak-f[1600] request (361 calls) from an `RV.State`: the witness that the assumptions of the
    split permutation claim can be met. x10 = 0 (call 0's control word), x11 = 0x400000 (the 31-slot state), RAM a
    byte pattern. Call `k`'s row is its worker's honest row read from the memory after calls `0 … k-1` at invocation
    clock `1 + 4 k`; the rows are a recursion over `k`, a run of consecutive blocks (`SequentialBlocks.run_blocks`), and
    every fact is proven by induction from the one-call lemmas (`Steps.lean`, `Calls.lean`), with no evaluation of the
    trace. -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Arithmetic Trace Keccak.Split Keccak.Split.Native

local notation "P" => babyBearModulus

/-- The starting state: control 0 in x10, the state pointer in x11, RAM a byte pattern. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 11 then 0x400000 else 0
  rom _ := 0
  mem address := BitVec.ofNat 8 (address.toNat * 37 + 11)

/-- The seed tokens read from `before`. -/
def seed : Memory := fun key => (cellOf key).initialToken (((cellOf key).readRV before).getD 0)

/-- The memory before call `k`. -/
def memAt : Nat → Memory
  | 0 => seed
  | k + 1 => runFinal (memAt k) ((memAt k).steps k)

/-- Call `k`'s row. -/
def rowAt (k : Nat) : Native.Row P := (memAt k).row k

/-- The run's steps of call `k`. -/
def stepsOf (k : Nat) : List (Nat × MemoryToken P) := (memAt k).steps k

def rows (n : Nat) : List (Native.Row P) := (List.range n).map rowAt

theorem seed_inv : Inv seed 0 where
  address _ _ := rfl
  clock _ _ := by simp [seed, Cell.initialToken, lastTouch, clockOf]
  high _ _ := rfl
  words key _ := seed_bounded (cellOf key) _
  control _ := by decide +kernel
  pointer := by decide +kernel

theorem inv_at (k : Nat) (small : k ≤ 361) : Inv (memAt k) k := by
  induction k with
  | zero => exact seed_inv
  | succ k ih =>
    have inv := ih (by omega)
    exact next inv (facts inv (by omega)) (by omega)

/-- The rows' memory steps are the run's edges from the seed, and the run ends at the memory after the calls. -/
theorem blocks : (rows 361).flatMap Native.Row.memorySteps = runEdges seed ((List.range 361).flatMap stepsOf) ∧
    runFinal seed ((List.range 361).flatMap stepsOf) = memAt 361 := by
  rw [rows, List.flatMap_map]
  exact run_blocks (mem := memAt) 361 (fun k _ => rfl) (fun k small => edges (facts (inv_at k (by omega)) small))

theorem inside : ∀ step ∈ (List.range 361).flatMap stepsOf, step.1 ∈ keys := by
  intro step member
  obtain ⟨n, present, current⟩ := List.mem_flatMap.mp member
  have small := List.mem_range.mp present
  have key : step.1 ∈ portKeys n := by
    rw [← step_keys (memAt n) n (facts (inv_at n (by omega)) small)]
    exact List.mem_map_of_mem current
  exact List.mem_range.mpr (portKeys_lt key)

theorem row_mem {n : Nat} {row : Native.Row P} (member : row ∈ rows n) : ∃ k < n, row = rowAt k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

/-- The invocation clock of call `k`. -/
theorem invocation_at (k : Nat) (call : k < 361) :
    decodeTimestamp (rowAt k).assignment (rowAt k).columns.invocation = ⟨1 + 4 * k, 0⟩ := by
  have rowFacts := facts (inv_at k (by omega)) call
  simp only [rowAt, decodeTimestamp, rowFacts.invocation, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, rowFacts.clockLow, rowFacts.clockHigh, Nat.cast_zero,
    ZMod.val_zero]
  rw [ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)]

/-- Every row is active. -/
theorem active_at (k : Nat) : (rowAt k).assignment (rowAt k).columns.execute = 1 := by
  unfold rowAt
  by_cases parity : k % 15 < 5
  · rw [Parity.row_eq (parity_kind (k := k) parity)]
    exact Nat.cast_one
  · by_cases theta : k % 15 < 10
    · rw [ThetaRho.row_eq (theta_kind (k := k) (by omega) theta)]
      exact Nat.cast_one
    · rw [Chi.row_eq (chi_kind (k := k) (by omega))]
      exact Nat.cast_one

def data : MemoryData P where
  rows := rows 361
  initial := keys.map seed
  terminal := keys.map (memAt 361)

theorem accepted : MemoryAccepted data where
  constraints row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    exact holds (inv_at k (by omega)) small
  matching := by
    have run := run_matching List.nodup_range seed inside
    rw [blocks.2] at run
    simp only [MemoryData.steps, data, blocks.1]
    exact run

theorem readable : ∀ cell ∈ cells, (cell.readRV before).isSome := by decide +kernel

theorem memory_inputs : RVMemoryInputs data before cells where
  initialization := by
    rw [initial_image readable, cells, List.map_map]
    rfl
  distinct := by decide +kernel
  clockRoom row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    rw [invocation_at k small]
    simp only [timestampBase]
    omega
  invocationHigh row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    rw [invocation_at k small]
    show 0 < timestampBase
    decide

theorem call_inputs : RVCallInputs data before cells where
  memory := memory_inputs
  controlCell := by decide +kernel
  controlStart := by decide +kernel
  active row member := by
    obtain ⟨k, small, rfl⟩ := row_mem member
    exact active_at k
  calls := by simp [data, rows]

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide +kernel

end Airbender.NonVacuous.KeccakSplitSpan
