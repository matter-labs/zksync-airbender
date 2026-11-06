import Slop.KeccakSplit.Setup.ThetaRho.Rows

/- Membership in the exported theta/rho table (`ThetaRho.setup`) over BabyBear, by tag:
   byte XOR (4), XOR-and-split (58), control (59), slots (60). Padding rows have tag 0,
   so a fixed nonzero tag excludes them. -/

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs

open Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

/-- A row of the exported table is a formula row. -/
theorem isFormulaRow {row : Vector (ZMod babyBearModulus) 9}
    (sound : (ThetaRho.setup (p := babyBearModulus)).toRaw.Soundness #[] row) :
    IsFormulaRow row := by
  change ∃ i : Fin thetaRhoSetup.traceLen,
    row = (setupRow thetaRhoSetup 9 i.val).map (fun v : Int => (v : ZMod babyBearModulus))
    at sound
  obtain ⟨⟨i, hi⟩, rfl⟩ := sound
  rw [traceLen_eq] at hi
  refine ⟨i, hi, ?_⟩
  rw [setupRow_eq i hi, Vector.map_map]
  congr 1

variable {row : Vector (ZMod babyBearModulus) 9}
  (sound : (ThetaRho.setup (p := babyBearModulus)).toRaw.Soundness #[] row)
include sound

/-- Tag 4: bounded bytes and their XOR. -/
theorem xor_byte_table_sound (tag : row[8] = 4) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ row[1].val ∧ (∀ c : Fin 5, row[3 + c.val] = 0) := by
  obtain ⟨h0, h1, h2, hx, z3, z4, z5, z6, z7⟩ := xor_facts (isFormulaRow sound) tag
  refine ⟨h0, h1, h2, hx, fun c => ?_⟩
  fin_cases c
  exacts [z3, z4, z5, z6, z7]

/-- Tag 58: both fragments of the XOR of two bytes rotated by `s < 8`. -/
theorem split_table_sound (tag : row[8] = 58) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 8 ∧
      row[3].val < 256 ∧ row[4].val < 256 ∧
      row[3].val = (row[0].val ^^^ row[1].val) * 2 ^ row[2].val % 256 ∧
      row[4].val = (row[0].val ^^^ row[1].val) / 2 ^ (8 - row[2].val) ∧
      (∀ c : Fin 3, row[5 + c.val] = 0) := by
  obtain ⟨h0, h1, h2, h3, h4, e3, e4, z5, z6, z7⟩ := split_facts (isFormulaRow sound) tag
  refine ⟨h0, h1, h2, h3, h4, e3, e4, fun c => ?_⟩
  fin_cases c
  exacts [z5, z6, z7]

/-- Tag 59, executed: the control transition and iteration flags of a theta/rho call. -/
theorem control_table_sound (tag : row[8] = 59) (active : row[1] = 1) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      row[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      row[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ c : Fin 5, row[3 + c.val] = if c.val = index.val % 5 then 1 else 0) := by
  obtain ⟨index, kind, c0, c2, f3, f4, f5, f6, f7⟩ := control_facts (isFormulaRow sound) tag active
  refine ⟨index, kind, c0, c2, fun c => ?_⟩
  fin_cases c
  exacts [f3, f4, f5, f6, f7]

/-- Tag 59, executed: a one-hot selector in columns 3..7. -/
theorem control_table_one_hot (tag : row[8] = 59) (active : row[1] = 1) :
    ∃ selected : Fin 5, ∀ c : Fin 5, row[3 + c.val] = if c = selected then 1 else 0 := by
  obtain ⟨index, -, -, -, flags⟩ := control_table_sound sound tag active
  refine ⟨⟨index.val % 5, Nat.mod_lt _ (by decide)⟩, fun c => ?_⟩
  rw [flags c]
  by_cases hc : c.val = index.val % 5
  · rw [ite_eq_left hc, ite_eq_left (Fin.ext hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun e => hc (congrArg Fin.val e))]

/-- Tag 59: the execute column is boolean. -/
theorem control_table_execute (tag : row[8] = 59) : row[1] = 0 ∨ row[1] = 1 :=
  control_execute (isFormulaRow sound) tag

/-- Tag 60 keyed by call `index` (control + 2048): that call's seven slots. -/
theorem slot_table_sound (tag : row[8] = 60) (index : Fin 361)
    (key : row[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)) :
    ∀ lane : Fin 7, row[1 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := slot_facts (isFormulaRow sound) tag index key
  intro lane
  fin_cases lane
  exacts [s1, s2, s3, s4, s5, s6, s7]

end Airbender.Keccak.Split.ThetaRho.SetupProofs
