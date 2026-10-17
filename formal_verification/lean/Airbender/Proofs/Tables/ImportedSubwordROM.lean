import Airbender.Proofs.Tables.ImportedROMProgram
import Airbender.Proofs.Tables.SubwordCharacterization
import Airbender.Proofs.Tables.ImportedROMReads
import Airbender.Proofs.Tables.ConstantTail
import Airbender.Proofs.Tables.ImportedSubwordROMData

namespace Airbender.Verification.SubwordROMGeometry
open Setup Setup.Proofs
open Airbender.Trace.ROM.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private abbrev cutoff := romCutoff
private abbrev publicProgram := Airbender.Trace.ROM.importedWords

private theorem program_index_bound (byte : Bool) (index : Nat)
    (bound : index < (subwordROMData byte).length) :
    index / (if byte then 8 else 4) < 1048576 := by
  cases byte
  · change index < 4194304 at bound
    change index / 4 < 1048576
    omega
  · change index < 8388608 at bound
    change index / 8 < 1048576
    omega

private theorem zero_slots (row : Vector Nat 9) (low : row[1] = 0) (high : row[2] = 0) :
    row = ((row.set 1 0).set 2 0) := by
  apply Vector.ext
  intro lane hLane
  by_cases one : lane = 1
  · subst lane
    simpa [Vector.getElem_set] using low
  · by_cases two : lane = 2
    · subst lane
      simpa [Vector.getElem_set] using high
    · simp only [Vector.getElem_set, if_neg (Ne.symm one), if_neg (Ne.symm two)]

private theorem program_row_congr (left right : Nat → BitVec 32) (byte : Bool) (index : Nat)
    (word : left (index / (if byte then 8 else 4)) = right (index / (if byte then 8 else 4))) :
    subwordProgramROMRow left byte index = subwordProgramROMRow right byte index := by
  simp only [subwordProgramROMRow, word]

/-- Actual native halfword and byte ROM output columns agree with the independently
    imported selected image. This includes every signed/high-half/high-byte
    control combination and every zero-padded word. -/
theorem imported_subword_rom (byte : Bool) (index : Nat)
    (bound : index < (subwordROMData byte).length) :
    subwordROMRow byte index = subwordProgramROMRow publicProgram byte index := by
  by_cases early : index < cutoff byte
  · exact rom_early_rows byte ⟨index, early⟩
  · have actual (lane : Fin 2) :
        (subwordROMData byte).columns[lane.val + 1].get? index = some 0 :=
      constantTail_sound _ _ _ (rom_tail_checked byte lane) index (Nat.le_of_not_gt early)
        (by rw [rom_tail_extent]; exact bound)
    have zeroProgram : publicProgram (index / (if byte then 8 else 4)) = 0 := by
      change BitVec.ofNat 32 (selectedWord (index / (if byte then 8 else 4))) = 0
      rw [selectedWord_zero]
      · rfl
      · cases byte <;> simp only [cutoff, romCutoff, Bool.false_eq_true, reduceIte] at early ⊢ <;> omega
      · exact program_index_bound byte index bound
    have zeroOutputs : subwordImportedLimbs byte
        (0 + 65536 * (index / ((if byte then 8 else 4) / 2) % 2) +
          131072 * (if byte then index % 2 else 0)) = (0, 0) := by
      rw [subwordImportedLimbs_eq_reference byte
        (0 + 65536 * (index / ((if byte then 8 else 4) / 2) % 2) +
          131072 * (if byte then index % 2 else 0))
        (by cases byte <;> simp only [Bool.false_eq_true, reduceIte, Nat.reduceDiv] <;> omega)]
      cases byte <;> simp [subwordLoadLimbs, Nat.add_mod, Nat.mul_mod]
    have outputs : subwordProgramROMRow publicProgram byte index =
        ((subwordROMRow byte index).set 1 0).set 2 0 := by
      simp only [subwordProgramROMRow, zeroProgram, show (0 : BitVec 32).toNat = 0 from rfl,
        Nat.zero_div, Nat.zero_mod, zeroOutputs]
    have low : (subwordROMRow byte index)[1] = 0 := by
      simpa [subwordROMRow] using congrArg (fun value => value.getD 0) (actual 0)
    have high : (subwordROMRow byte index)[2] = 0 := by
      simpa [subwordROMRow] using congrArg (fun value => value.getD 0) (actual 1)
    exact (zero_slots (subwordROMRow byte index) low high).trans outputs.symm

/-- Bind the actual native output columns to an arbitrary starting Sail state
    whose public bytes equal this complete imported image. -/
theorem imported_subword_rom_before {before : Reference.RiscV.Sail.State}
    (image : Airbender.Trace.ROM.ImportedImage before) (byte : Bool) (index : Nat)
    (bound : index < (subwordROMData byte).length) :
    subwordROMRow byte index = subwordProgramROMRow (Airbender.Trace.ROM.words before) byte index := by
  have wordBound := program_index_bound byte index bound
  exact (imported_subword_rom byte index bound).trans
    (program_row_congr publicProgram (Airbender.Trace.ROM.words before) byte index
      (imported_image_words image (index / (if byte then 8 else 4)) wordBound).symm)

/-- The concrete selected setup replaces both program-dependent ROM outputs;
    the arbitrary-program theorem remains available through its proven view. -/
theorem imported_subword_row_before {before : Reference.RiscV.Sail.State}
    (image : Airbender.Trace.ROM.ImportedImage before) (index : Fin 13238273) :
    importedSubwordRow index = subwordNativeRow (Airbender.Trace.ROM.words before) index := by
  by_cases fixed : index.val < subwordROMHalfDataRegion.offset
  · have shape : importedSubwordRow index = subwordNativeRow (fun _ => 0) index := by
      simp only [importedSubwordRow, if_pos fixed]
    exact shape.trans (subword_fixed_independent _ _ index fixed)
  · have notfixed : ¬index.val < 655361 := fixed
    by_cases half : index.val < subwordROMByteDataRegion.offset
    · have isHalf : index.val < 4849665 := half
      have shape : importedSubwordRow index = subwordROMRow false (index.val - 655361) := by
        simp only [importedSubwordRow,
          show subwordROMHalfDataRegion.offset = 655361 from rfl, if_neg notfixed, if_pos half]
      exact shape.trans ((imported_subword_rom_before image false (index.val - 655361)
        (by change index.val - 655361 < 4194304; change ¬index.val < 655361 at fixed;
            change index.val < 4849665 at half; omega)).trans
              (subword_half_slice _ index (by change ¬index.val < 655361 at fixed; omega) half).symm)
    · have notHalf : ¬index.val < 4849665 := half
      have shape : importedSubwordRow index = subwordROMRow true (index.val - 4849665) := by
        simp only [importedSubwordRow, if_neg fixed,
          show subwordROMByteDataRegion.offset = 4849665 from rfl, if_neg notHalf]
      exact shape.trans ((imported_subword_rom_before image true (index.val - 4849665)
        (by have := index.isLt; change index.val - 4849665 < 8388608; omega)).trans
          (subword_byte_slice _ index (by change ¬index.val < 4849665 at half; omega)).symm)

theorem imported_subword_table_before {p : Nat} [Fact p.Prime]
    {before : Reference.RiscV.Sail.State} (image : Airbender.Trace.ROM.ImportedImage before) :
    importedSubwordTable (p := p) = subwordTable (Airbender.Trace.ROM.words before) := by
  change subwordTableOfRows (p := p) importedSubwordRow =
    subwordTableOfRows (p := p) (subwordNativeRow (Airbender.Trace.ROM.words before))
  exact congrArg (subwordTableOfRows (p := p)) (funext (imported_subword_row_before image))

end Airbender.Verification.SubwordROMGeometry
