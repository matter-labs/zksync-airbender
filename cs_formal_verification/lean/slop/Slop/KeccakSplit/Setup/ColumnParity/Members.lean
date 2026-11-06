import Slop.KeccakSplit.Setup.ColumnParity.Rows

/- Membership in the exported column-parity table (`ColumnParity.setup`) over BabyBear,
   by tag: iota byte XOR (38), slots (62), control (63), five-nibble XOR (64). Padding
   rows have tag 0, so a fixed nonzero tag excludes them. -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- A row of the exported table is a formula row. -/
theorem isFormulaRow {row : Vector (ZMod babyBearModulus) 8}
    (sound : (ColumnParity.setup (p := babyBearModulus)).toRaw.Soundness #[] row) :
    IsFormulaRow row := by
  change ∃ i : Fin columnParitySetup.traceLen,
    row = (setupRow columnParitySetup 8 i.val).map (fun v : Int => (v : ZMod babyBearModulus))
    at sound
  obtain ⟨⟨i, hi⟩, rfl⟩ := sound
  rw [traceLen_eq] at hi
  refine ⟨i, hi, ?_⟩
  rw [setupRow_eq i hi, Vector.map_map]
  congr 1

variable {row : Vector (ZMod babyBearModulus) 8}
  (sound : (ColumnParity.setup (p := babyBearModulus)).toRaw.Soundness #[] row)
include sound

/-- Tag 64: bounded nibble inputs and their exact five-input XOR. -/
theorem xor5_table_sound (tag : row[7] = 64) :
    (∀ c : Fin 5, row[c.val].val < 16) ∧ row[5].val < 16 ∧
      row[5].val = row[0].val ^^^ row[1].val ^^^ row[2].val ^^^ row[3].val ^^^ row[4].val ∧
      row[6] = 0 := by
  obtain ⟨⟨h0, h1, h2, h3, h4⟩, h5, hx, h6⟩ := xor5_facts (isFormulaRow sound) tag
  refine ⟨fun c => ?_, h5, hx, h6⟩
  fin_cases c
  exacts [h0, h1, h2, h3, h4]

/-- Tag 38: bounded bytes and the iota byte `a ^ iotaByte b`. -/
theorem iota_table_sound (tag : row[7] = 38) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ Airbender.Keccak.iotaByte row[1].val ∧
      (∀ c : Fin 4, row[3 + c.val] = 0) := by
  obtain ⟨h0, h1, h2, hx, z3, z4, z5, z6⟩ := iota_facts (isFormulaRow sound) tag
  refine ⟨h0, h1, h2, hx, fun c => ?_⟩
  fin_cases c
  exacts [z3, z4, z5, z6]

/-- Tag 63, executed: the control transition and iota round of a parity call. -/
theorem control_table_sound (tag : row[7] = 63) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .columnParity ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      row[3] = ((if index.val % 5 = 0 then index.val / 15 else 0 : Nat) : ZMod babyBearModulus) :=
  control_facts (isFormulaRow sound) tag active

/-- Tag 63: the execute column is boolean. -/
theorem control_table_execute (tag : row[7] = 63) : row[1] = 0 ∨ row[1] = 1 :=
  control_execute (isFormulaRow sound) tag

/-- Tag 62 keyed by call `index` (control + 2048): that call's six slots. -/
theorem slot_table_sound (tag : row[7] = 62) (index : Fin 361)
    (key : row[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)) :
    ∀ lane : Fin 6, row[1 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := slot_facts (isFormulaRow sound) tag index key
  intro lane
  fin_cases lane
  exacts [s1, s2, s3, s4, s5, s6]

end Airbender.Keccak.Split.ColumnParity.SetupProofs
