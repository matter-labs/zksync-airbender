import Tests.AddSub

namespace Tests.PC
open Airbender Arithmetic Reference.RiscV

private def wrapRow := Tests.AddSub.row 1 123 123 0 246 0 0 0 65532 65535 0 0 1 1

theorem wrap_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment wrapRow) AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, wrapRow, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private def input : Sail.Input where
  row := ⟨.add, ⟨123, 0⟩, ⟨123, 0⟩, ⟨0, 0⟩, ⟨65532, 65535⟩⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 1
  rd := .Regidx 1
  encodedImmediate := 0
  encodedUpperImmediate := 0
  before := default

theorem native_pc_wrap : (⟨0, 0⟩ : Word).toBitVec = (⟨65532, 65535⟩ : Word).toBitVec + 4 :=
  (AddSub.Proofs.pc_successor (by decide) wrap_satisfies
    (input := input) (output := ⟨⟨246, 0⟩, ⟨0, 0⟩⟩)
    (by constructor <;> decide) ⟨by decide, by decide⟩ (by decide)).2

end Tests.PC
