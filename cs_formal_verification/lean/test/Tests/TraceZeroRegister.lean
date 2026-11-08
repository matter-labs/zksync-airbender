import Slop.Trace.RowHistory
import Human.Helpers.Memory.ROM
import Slop.Trace.Timestamps
import Human.Helpers.Decoder.Instruction
import Slop.AddSub.Selectors
import Slop.Trace.Family.Values
import Slop.Trace.PC
import Human.Helpers.Core.BabyBearPrime

namespace Tests.TraceZeroRegister
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- Original ADD x0,x1,x2 becomes a native ADD with three x0 accesses.
-- Repeated reads use the preceding native refresh writes, at clocks 4 and 5.
def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 21 => 8
  | 35 => 5
  | 4 | 10 | 42 | 43 | 44 => 1
  | _ => 0
def row : Row babyBearModulus := ⟨.addSub, assignment⟩
private def token (time : Nat) : MemoryToken babyBearModulus := ⟨0, (time, 0), 0⟩
private def cells : List Cell := [.register 0, .register 1, .register 2]
private def sourceTokens : List (MemoryToken babyBearModulus) :=
  [(Cell.register 1).initialToken 5, (Cell.register 2).initialToken 7]
private def rom : Table (ZMod babyBearModulus) (fields 9) := ROM.table cells (token 0 :: sourceTokens)
private def trace : Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := token 0 :: sourceTokens
  terminalMemory := token 6 :: sourceTokens
theorem local_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro source member
    simp only [trace, sourceTokens, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private def mutated (index : Nat) : ZMod babyBearModulus :=
  if index = 33 then 1 else assignment index

theorem nonzero_native_output_rejected : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment mutated) AddSub.importedConstraints := by
  intro constraints
  have result := AddSub.Proofs.zero_operands_result (by decide) constraints rfl (by
    intro k lower upper
    interval_cases k <;> rfl) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  change (Word.mk 1 0).toBitVec = 0 at result
  contradiction

end Tests.TraceZeroRegister
