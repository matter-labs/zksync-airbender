import Airbender.Proofs.AddSub.RowClaims
import Airbender.Review.Circuits.AddSub.Theorems
import Airbender.Proofs.Sail.PC

namespace Tests.PC
open Airbender
open Airbender.Reference.RiscV
open Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail

-- Active ADD x1,x1,x1, with a PC carry across the 16-bit boundary.
private def row (i : Nat) : ZMod babyBearModulus :=
  if i = 0 then 65535 else if i = 4 ∨ i = 7 ∨ i = 10 ∨ i = 20 then 1
  else if i = 19 then 3 else if i = 21 then 4
  else if i = 25 ∨ i = 29 then 123 else if i = 41 then 1447027789
  else if i = 33 then 246 else 0

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       decide)

example : (⟨3, 1⟩ : Arithmetic.Word).value = (⟨65535, 0⟩ : Arithmetic.Word).value + 4 :=
  (AddSub.Proofs.pc_successor (by decide) (by decide) satisfies
    (by constructor <;> decide)
    ⟨by decide, by decide⟩).1

private def before : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (65535 : BitVec 32)) }

private def input : Input where
  row := ⟨.add, ⟨123, 0⟩, ⟨123, 0⟩, ⟨0, 0⟩, ⟨65535, 0⟩⟩
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
  · intro _
    exact ⟨123, read, fun _ => rfl⟩
  · intro _
    exact ⟨123, read, fun _ => rfl⟩
  · simp [input]
  · simp [input]
  · apply read_register
    simp [input, before, Arithmetic.Word.toBitVec, Arithmetic.Word.value]

/-- Both sources and the destination alias; reads precede the native write and PC retirement. -/
example : spec input ⟨⟨246, 0⟩, ⟨3, 1⟩⟩ := by
  apply step_of_destination contract (by decide)
  intro state hc
  apply spec_of_result hc (by change input.rd ≠ zeroRegister; decide)
  change (246 : BitVec 32) = (123 : BitVec 32) + 123
  decide

end Tests.PC
