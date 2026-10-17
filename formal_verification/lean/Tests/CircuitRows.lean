import Tests.AddSub

namespace Tests.CircuitRows
open Airbender

theorem addi_carry_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 2 65535 0 1 0 1 1 0 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem sub_borrow_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 4 0 1 0 65535 65535 1 1 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem lui_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 8 0 0 4096 4096 0 0 0 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem auipc_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment
      (Tests.AddSub.row 16 0 0 4096 4096 0 0 0 0 0 4 0 0 0))
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private def zeroRow (i : Nat) : ZMod mersenne31Modulus :=
  if i = 7 then 0 else if i = 8 then 1 else Tests.AddSub.row 1 0 0 0 0 0 0 0 0 0 4 0 0 0 i

theorem discarded_write_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroRow)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, zeroRow, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

open Reference.RiscV.Sail Reference.Sail Arithmetic

-- V2 retains SUB (mask 4) and its nonzero operands when rd=x0; only its write is masked.
private def x0SubRow (i : Nat) : ZMod mersenne31Modulus :=
  if i = 6 then 2 else if i = 7 ∨ i = 37 then 0 else if i = 8 then 1
  else Tests.AddSub.row 4 5 3 0 2 0 0 0 0 0 4 0 0 0 i

theorem x0_sub_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment x0SubRow)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, x0SubRow, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private def x0Before : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (5 : BitVec 32) |>.insert .x2 (3 : BitVec 32)
      |>.insert .PC (0 : BitVec 32)) }

private def x0Input : Input where
  row := ⟨.sub, ⟨5, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := .Regidx 0
  encodedImmediate := 0
  encodedUpperImmediate := 0
  before := x0Before

private theorem x0Contract : Contract x0Input := by
  have left : run (SailRV32.Functions.rX_bits x0Input.rs1) x0Before =
      .ok (5 : BitVec 32) x0Before := by
    apply read_register
    simp [x0Before, Std.ExtDHashMap.get?_insert]
  have right : run (SailRV32.Functions.rX_bits x0Input.rs2) x0Before =
      .ok (3 : BitVec 32) x0Before := by
    apply read_register
    simp [x0Before, Std.ExtDHashMap.get?_insert]
  constructor
  · intro _; exact ⟨5, left, fun impossible => (impossible rfl).elim⟩
  · intro _; exact ⟨3, right, fun impossible => (impossible rfl).elim⟩
  · simp [x0Input]
  · simp [x0Input]
  · apply read_register
    simp [x0Input, x0Before, Word.toBitVec, Word.value]

/-- Apply the public theorem to original Sail SUB x0,x1,x2 with nonzero operands. -/
theorem x0_sub_execution : spec x0Input ⟨⟨0, 0⟩, ⟨4, 0⟩⟩ := by
  apply Airbender.AddSub.mersenne31_soundness x0Input _ x0SubRow
  refine ⟨?_, x0_sub_satisfies, ?_⟩
  · constructor
    · decide
    · decide
    · simp [Airbender.AddSub.Preprocessing, x0Input]
    · intro impossible; exact (impossible rfl).elim
    · constructor <;> decide
    · decide
    · exact x0Contract
  · constructor <;> decide

end Tests.CircuitRows
