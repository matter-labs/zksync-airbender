import Airbender.Import.Embed
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2Round

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- Native Clean equations and queries; setup provenance and memory transport remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/blake2_with_extended_control_layout_no_caches_gkr.json" blake_round_lookups

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 352 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 210 := rfl

namespace Variables
abbrev execute := 0
abbrev controlReadLo := 135
abbrev controlReadHi := 136
abbrev controlWriteLo := 137
abbrev controlWriteHi := 138
abbrev controlBits := #v[139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def stateReads : Vector (Nat × Nat) 8 := Vector.ofFn fun i => (5 + 4 * i.val, 6 + 4 * i.val)
def extendedReads : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (37 + 4 * i.val, 38 + 4 * i.val)
def messageReads : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (103 + 2 * i.val, 104 + 2 * i.val)
def chainingInputs : Vector (Nat × Nat) 8 :=
  #v[(154, 156), (158, 160), (162, 164), (166, 168),
    (170, 172), (174, 176), (178, 180), (182, 184)]
def preparedState : Vector (Nat × Nat) 16 :=
  #v[(155, 157), (159, 161), (163, 165), (167, 169),
    (171, 173), (175, 177), (179, 181), (183, 185),
    (186, 187), (188, 189), (190, 191), (192, 193),
    (198, 199), (194, 195), (200, 201), (196, 197)]
def preparedMessage : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (204 + 2 * i.val, 205 + 2 * i.val)
abbrev roundBits := #v[142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def scheduledMessage : Vector (Nat × Nat) 16 := Vector.ofFn fun i => (236 + 2 * i.val, 237 + 2 * i.val)
end Variables

theorem variable_roles :
    importedConstraintsVariableNames.lookup 0 = some "Execute flag for cycle" ∧
    importedConstraintsVariableNames.lookup 135 = some "control read/write from x12 read[0]" ∧
    importedConstraintsVariableNames.lookup 136 = some "control read/write from x12 read[1]" ∧
    importedConstraintsVariableNames.lookup 137 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 138 = some "control read/write from x12 write[0]" ∧
    importedConstraintsVariableNames.lookup 152 = some "perform final xor flag" := by
  repeat' apply And.intro
  all_goals decide

theorem pointer_roles :
    importedConstraintsVariableNames.lookup 3 = some "state read/write from x10 read[0]" ∧
    importedConstraintsVariableNames.lookup 4 = some "state read/write from x10 read[1]" ∧
    importedConstraintsVariableNames.lookup 101 = some "input read from x11 read[0]" ∧
    importedConstraintsVariableNames.lookup 102 = some "input read from x11 read[1]" := by
  repeat' apply And.intro
  all_goals decide

/-- The input-word mappings agree with the labels in the imported artifact.
    This guards numbering; global memory transport is a separate interface. -/
theorem preparation_roles :
    (∀ i : Fin 8,
      importedConstraintsVariableNames.lookup Variables.stateReads[i].1 =
        some s!"state read/write from x10 indirect access {i.val} read[0]" ∧
      importedConstraintsVariableNames.lookup Variables.stateReads[i].2 =
        some s!"state read/write from x10 indirect access {i.val} read[1]") ∧
    (∀ i : Fin 16,
      importedConstraintsVariableNames.lookup Variables.extendedReads[i].1 =
        some s!"state read/write from x10 indirect access {8 + i.val} read[0]" ∧
      importedConstraintsVariableNames.lookup Variables.extendedReads[i].2 =
        some s!"state read/write from x10 indirect access {8 + i.val} read[1]") ∧
    (∀ i : Fin 16,
      importedConstraintsVariableNames.lookup Variables.messageReads[i].1 =
        some s!"input read from x11 indirect access {i.val} read[0]" ∧
      importedConstraintsVariableNames.lookup Variables.messageReads[i].2 =
        some s!"input read from x11 indirect access {i.val} read[1]") := by
  refine ⟨?_, ?_, ?_⟩
  all_goals intro i
  all_goals fin_cases i <;>
    simp only [Variables.stateReads, Variables.extendedReads, Variables.messageReads,
      Fin.getElem_fin, Vector.getElem_ofFn] <;> decide

end Airbender.Blake2Round
