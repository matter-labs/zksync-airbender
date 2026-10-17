import Airbender.Review.Circuits.AddSub.Theorems

namespace Tests.AddSub
open Airbender Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail

-- Initialized timestamp 4, preceding timestamps zero, and three strict borrows.
-- Explicit native PC inverse witnesses cover zero PC and the full rollover fixture.
def row (mask a b imm resultLo resultHi carry wrap pcLo pcHi nextLo nextHi pcCarry pcWrap : Nat)
    (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then pcLo else if i = 1 then pcHi else if i = 2 then 4
  else if i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 46 ∨ i = 49 ∨ i = 52 then 1
  else if i = 9 then imm else if i = 12 then mask
  else if i = 13 then nextLo else if i = 14 then nextHi else if i = 15 then 8
  else if i = 17 then if mask = 1 then 1 else 0
  else if i = 18 then if mask = 2 then 1 else 0
  else if i = 19 then if mask = 4 then 1 else 0
  else if i = 20 then if mask = 8 then 1 else 0
  else if i = 21 then if mask = 16 then 1 else 0
  else if i = 25 then a else if i = 27 then b
  else if i = 29 ∨ i = 37 then resultLo else if i = 30 ∨ i = 38 then resultHi
  else if i = 33 then wrap else if i = 34 then a * b
  else if i = 39 then if pcLo = 0 then 1227138194 else 0
  else if i = 40 then pcCarry
  else if i = 41 then if pcHi + pcCarry = 0 then 2147450879 else 0
  else if i = 42 then pcWrap else if i = 43 then carry else 0

private def addRow := row 1 123 123 0 246 0 0 0 0 0 4 0 0 0

theorem add_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment addRow) Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, addRow, row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private def before : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32)) }

private def input : Input where
  row := ⟨.add, ⟨123, 0⟩, ⟨123, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 1
  rd := .Regidx 1
  encodedImmediate := 0
  encodedUpperImmediate := 0
  before := before

private theorem contract : Contract input := by
  have read : run (SailRV32.Functions.rX_bits input.rs1) before = .ok (123 : BitVec 32) before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  constructor
  · intro _; exact ⟨123, read, fun _ => rfl⟩
  · intro _; exact ⟨123, read, fun _ => rfl⟩
  · simp [input]
  · simp [input]
  · apply read_register
    simp [input, before, Word.toBitVec, Word.value]

private theorem interfaces : Airbender.AddSub.InterfaceAssumptions input ⟨⟨246, 0⟩, ⟨4, 0⟩⟩ addRow := by
  constructor
  · decide
  · decide
  · rfl
  · intro _; constructor <;> constructor <;> decide
  · constructor <;> decide
  · decide
  · exact contract

private theorem mapping : Airbender.AddSub.RowWordMapping input ⟨⟨246, 0⟩, ⟨4, 0⟩⟩ addRow := by
  constructor <;> decide

/-- A nonvacuous application of the public native-field theorem to aliased sources/destination. -/
theorem add_execution : spec input ⟨⟨246, 0⟩, ⟨4, 0⟩⟩ :=
  Airbender.AddSub.mersenne31_soundness input _ addRow ⟨interfaces, add_satisfies, mapping⟩

theorem changed_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun i => if i = 37 then 247 else addRow i))
      Airbender.AddSub.importedConstraints := by
  intro h
  have bad := Verification.assertion_of_holds h ⟨24, by rw [Airbender.AddSub.Proofs.constraint_count]; decide⟩
  revert bad
  decide

end Tests.AddSub
