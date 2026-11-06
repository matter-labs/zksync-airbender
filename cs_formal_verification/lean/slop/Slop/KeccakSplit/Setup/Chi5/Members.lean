import Slop.KeccakSplit.Setup.Chi5.Rows

/- Membership in the exported chi5 table (`Chi5.setup`) over BabyBear, by tag: chi (65)
   and control (66). Padding rows have tag 0, so a fixed nonzero tag excludes them. -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- A row of the exported table is a formula row. -/
theorem isFormulaRow {row : Vector (ZMod babyBearModulus) 11}
    (sound : (Chi5.setup (p := babyBearModulus)).toRaw.Soundness #[] row) :
    IsFormulaRow row := by
  change ∃ i : Fin chi5Setup.traceLen,
    row = (setupRow chi5Setup 11 i.val).map (fun v : Int => (v : ZMod babyBearModulus))
    at sound
  obtain ⟨⟨i, hi⟩, rfl⟩ := sound
  rw [traceLen_eq] at hi
  refine ⟨i, hi, ?_⟩
  rw [setupRow_eq i hi, Vector.map_map]
  congr 1

variable {row : Vector (ZMod babyBearModulus) 11}
  (sound : (Chi5.setup (p := babyBearModulus)).toRaw.Soundness #[] row)
include sound

/-- Tag 65: bounded nibble inputs and chi of each, `a ^ (!b & c)` on four bits. -/
theorem chi_table_sound (tag : row[10] = 65) :
    (∀ c : Fin 5, row[c.val].val < 16) ∧
      (∀ c : Fin 5, row[5 + c.val].val < 16 ∧
        row[5 + c.val].val = row[c.val].val ^^^
          ((15 ^^^ row[(c.val + 1) % 5].val) &&& row[(c.val + 2) % 5].val)) := by
  obtain ⟨⟨b0, b1, b2, b3, b4⟩, ⟨o5, o6, o7, o8, o9⟩, x5, x6, x7, x8, x9⟩ :=
    chi_facts (isFormulaRow sound) tag
  refine ⟨fun c => ?_, fun c => ?_⟩
  · fin_cases c
    exacts [b0, b1, b2, b3, b4]
  · fin_cases c
    exacts [⟨o5, x5⟩, ⟨o6, x6⟩, ⟨o7, x7⟩, ⟨o8, x8⟩, ⟨o9, x9⟩]

/-- Tag 66, executed: the control transition, five slots and plane of a chi call. -/
theorem control_table_sound (tag : row[10] = 66) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .chi5 ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 5, row[3 + lane.val] =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) ∧
      row[8] = ((index.val % 5 : Nat) : ZMod babyBearModulus) := by
  obtain ⟨index, kind, c0, c2, ⟨s3, s4, s5, s6, s7⟩, c8⟩ :=
    control_facts (isFormulaRow sound) tag active
  refine ⟨index, kind, c0, c2, fun lane => ?_, c8⟩
  fin_cases lane
  exacts [s3, s4, s5, s6, s7]

/-- Tag 66: the plane column is below five. -/
theorem control_table_plane (tag : row[10] = 66) : row[8].val < 5 :=
  control_plane (isFormulaRow sound) tag

/-- Tag 66: the execute column is boolean. -/
theorem control_table_execute (tag : row[10] = 66) : row[1] = 0 ∨ row[1] = 1 :=
  control_execute (isFormulaRow sound) tag

end Airbender.Keccak.Split.Chi5.SetupProofs
