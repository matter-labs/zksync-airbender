module
public import Proven.NonVacuous.KeccakSpan.Tables
public import Proven.NonVacuous.KeccakSpan.Route
public import Human.Helpers.Context.Timestamps

@[expose] public section

/-! The ranges an honest Keccak row needs (`RowInput.Valid`): 16-bit lanes read, a 256-aligned pointer, previous
    clocks below the write clock, and an invocation clock that is 1 mod 4 with room for the writes. Under them every
    operation of the row is valid (its operands are lanes read, Iota constants or earlier 16-bit results). -/

namespace Airbender.NonVacuous.KeccakSpan

/-- The ranges of a row's inputs. -/
structure RowInput.Valid (x : RowInput) : Prop where
  read : ∀ lane < 6, ∀ j < 4, x.read lane j < 65536
  pointer : x.pointer.lo < 65536 ∧ x.pointer.hi < 65536 ∧ x.pointer.lo % 256 = 0
  previous : ∀ port < 14, x.previous port < x.invocation + 2
  invocation : x.invocation % 4 = 1
  room : x.invocation + 2 < Trace.timestampBase

namespace RowInput
variable {x : RowInput}

theorem iotaB_lt (j : Nat) (hj : j < 4) : x.iotaB j < 65536 := by
  have round : x.round < 32 := x.state.round.isLt
  simp only [RowInput.iotaB, RowInput.iotaRound]
  split_ifs <;> omega

set_option hygiene false in
/-- An operation's validity, mode by mode: its operands are lanes read, Iota constants or earlier results. -/
local macro "operands " k:ident : tactic => `(tactic| (
  rcases RowInput.modes x with hm | hm | hm | hm | hm | hm | hm <;>
  simp only [$k:ident, hm, ↓reduceIte, Nat.reduceEqDiff, Op.byte, Op.rotate] <;>
  refine ⟨fun j hj => ?_, fun _ j hj => ?_, fun _ => ?_⟩ <;>
  first
    | (simp only [Bool.true_eq_false] at *; done)
    | (simp only [true_or, or_true]; done)
    | exact valid.read _ (by decide) j hj
    | exact iotaB_lt j hj
    | exact earlier.out_lt hj))

theorem op0_valid (valid : x.Valid) : x.op0.Valid := by
  have earlier : (Op.byte 4 (fun _ => 0) (fun _ => 0)).Valid := ⟨by decide, by decide, by decide⟩
  operands RowInput.op0

theorem op1_valid (valid : x.Valid) : x.op1.Valid := by
  have earlier := op0_valid valid
  operands RowInput.op1

theorem op2_valid (valid : x.Valid) : x.op2.Valid := by
  have earlier := op1_valid valid
  operands RowInput.op2

theorem op3_valid (valid : x.Valid) : x.op3.Valid := by
  have earlier := op2_valid valid
  operands RowInput.op3

theorem op4_valid (valid : x.Valid) : x.op4.Valid := by
  have earlier := op3_valid valid
  operands RowInput.op4

end RowInput

end Airbender.NonVacuous.KeccakSpan
