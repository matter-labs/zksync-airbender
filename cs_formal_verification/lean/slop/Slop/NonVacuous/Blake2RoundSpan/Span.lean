module
public import Slop.NonVacuous.Blake2RoundSpan.From
public import Human.Trace.Workers.Blake2Round.RVCall
public import Human.Helpers.Delegation.Operations

@[expose] public section

/-! A complete ten-round extended-control Blake2s span (plain mode, flags 0) from an `RV.State`: the witness that the
    assumptions of the round compression, boundary and window claims can be met. x10 = 0x400000 (8 state and 16
    extended words), x11 = 0x400080 (16 message words), x12 = 0x80000 (round bit 0, no control flags), RAM a byte
    pattern: the span of `From.lean` from the seed at clock 1. -/

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

theorem seed_inv : Inv seed 1 0 where
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

theorem control_start : (Cell.register 12).readRV before = some (BitVec.ofNat 32 ((8 + (0 : Fin 8).val) * 65536)) := by
  decide +kernel

theorem calls : data.rows.length = if (0 : Fin 8).val % 2 = 1 then 7 else 10 := calls_from

theorem call_inputs : Blake2Round.RVCallInputs data before cells 0 where
  memory := memory_inputs
  tables := rfl
  family := family_from
  controlStart := control_start
  calls := calls

theorem native_call_inputs : Blake2Round.RVNativeCallInputs data before cells 0 where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family_from
  controlStart := control_start
  calls := calls

/-- The whole span is the window after an empty prefix: every row writes in `(0, 1000]`. -/
theorem window_inputs : Blake2Round.RVWindowInputs data before cells 0 0 1000 where
  memory := boundary_inputs memory_inputs
  tables := rfl
  family := family_from
  controlStart := control_start
  prefixEmpty := prefix_from start (by omega)
  roundsBound := Nat.le_of_eq calls_from
  calls := by
    rw [show data.windowRows 0 1000 = data.rows from window_from start (by omega) (by omega)]
    exact calls

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by
  simp only [cells, List.mem_map, List.mem_range]
  rintro _ ⟨j, hj, rfl⟩
  unfold cellAt
  split_ifs <;> simp only [Cell.Aligned, ramCell, stateBase, messageBase, Word.value, limbBase,
    BitVec.toNat_ofNat] <;> omega

end Airbender.NonVacuous.Blake2RoundSpan
