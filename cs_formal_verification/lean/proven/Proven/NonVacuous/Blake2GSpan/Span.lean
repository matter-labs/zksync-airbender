module
public import Proven.NonVacuous.Blake2GSpan.From
public import Proven.NonVacuous.Basic
public import Human.Trace.Workers.Blake2G.RVCall
public import Human.Helpers.Delegation.Operations

@[expose] public section

/-! A complete reduced G span (56 rows) from an `RV.State`: the witness that the assumptions of the Blake2s G
    work-vector, boundary and window claims can be met. x10 = 0x400000 (sixteen state words), x11 = 0x400040
    (sixteen message words), x12 = 128 (reduced mode, call 0), RAM a byte pattern: the span of `From.lean` from the
    seed at clock 1. -/

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

theorem seed_inv : Inv seed 1 where
  address _ _ := rfl
  high _ _ := rfl
  time _ _ := by simp [seed, Cell.initialToken]
  words c _ := seed_bounded c _
  state := by decide +kernel
  message := by decide +kernel
  control := by decide +kernel

/-- The span starts at the seed at clock 1. -/
theorem start : Start seed 1 := ⟨seed_inv, rfl, by decide⟩

noncomputable def data : Delegation.MemoryData P := workersFrom seed 1

theorem accepted : Delegation.MemoryAccepted data := accepted_from start

theorem readable : ∀ cell ∈ cells, (cell.readRV before).isSome := by decide +kernel

theorem memory_inputs : Delegation.RVMemoryInputs data before cells :=
  ⟨initial_image readable, by decide +kernel, clock_room_from start, invocation_high_from start⟩

theorem control_start : (Cell.register 12).readRV before = some (if true then 128 else 0) := by decide

theorem call_inputs : Blake2G.RVCallInputs data before cells true where
  memory := memory_inputs
  tables := rfl
  family := family_from
  active := active_from
  controlStart := control_start
  calls := calls_from

theorem native_call_inputs : Blake2G.RVNativeCallInputs data before cells true where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family_from
  active := active_from
  controlStart := control_start
  calls := calls_from

/-- The whole span is one window after an empty prefix: every row writes in `(0, 1000]`. -/
theorem window_inputs : Blake2G.RVWindowInputs data before cells true 0 1000 where
  memory := memory_inputs
  tables := rfl
  family := family_from
  active := active_from
  controlStart := control_start
  prefixComplete := by
    rw [show data.prefixRows 0 = [] from prefix_from start (by omega)]
    rfl
  calls := by
    rw [show data.windowRows 0 1000 = data.rows from window_from start (by omega) (by omega)]
    exact calls_from

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide +kernel

end Airbender.NonVacuous.Blake2GSpan
