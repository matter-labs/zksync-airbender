import Airbender.Proofs.UnifiedReduced.Tables.ImportedROMRows
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData
import Airbender.Proofs.Tables.ImportedROMProgram
import Airbender.Proofs.Tables.ImportedROMReads
import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem ofNatWord (value : Nat) (bound : value < 4294967296) :
    Arithmetic.Word.ofBitVec (BitVec.ofNat 32 value) =
      Arithmetic.Word.mk (value % 65536) (value / 65536) := by
  simp only [Arithmetic.Word.ofBitVec, BitVec.toNat_ofNat, Arithmetic.limbBase,
    Nat.mod_eq_of_lt bound]

private def romFields (address : Nat) (word : BitVec 32) : Vector Nat 10 :=
  #v[address, (Arithmetic.Word.ofBitVec word).lo,
    (Arithmetic.Word.ofBitVec word).hi, 0, 0, 0, 0, 0, 0, 34]

private theorem wordFields (address value : Nat) (bound : value < 4294967296) :
    (#v[address, value % 65536, value / 65536, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10) =
      romFields address (BitVec.ofNat 32 value) := by
  simp only [romFields, ofNatWord value bound]

/-- Public image equality connects the full native ROM view to the existing
    generalized table. It supplies bytes only; table outputs are conclusions. -/
theorem imported_row_before {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) (index : Fin 2097537) :
    importedRow index = row before index := by
  by_cases fixed : index.val < 1048961
  · simp only [importedRow, row, dif_pos fixed]
  · have bound : index.val - 1048961 < 1048576 := by have := index.isLt; omega
    simp only [importedRow, row, dif_neg fixed]
    have binding : Trace.ROM.words before (index.val - 1048961) =
        BitVec.ofNat 32 (Trace.ROM.Proofs.selectedWord (index.val - 1048961)) :=
      (Trace.ROM.Proofs.imported_image_words image (index.val - 1048961) bound).trans rfl
    exact (imported_rom_row (index.val - 1048961) bound).trans
      ((wordFields (4 * (index.val - 1048961))
        (Trace.ROM.Proofs.selectedWord (index.val - 1048961))
        (Trace.ROM.Proofs.selectedWord_bound (index.val - 1048961) bound)).trans
          (congrArg (romFields (4 * (index.val - 1048961))) binding.symm))

theorem imported_table_before {p : Nat} [Fact p.Prime]
    {before : Reference.RiscV.Sail.State} (image : Trace.ROM.ImportedImage before) :
    importedTable (p := p) = table before := by
  change tableOfRows (p := p) importedRow = tableOfRows (p := p) (row before)
  exact congrArg (tableOfRows (p := p)) (funext (imported_row_before image))

end Airbender.UnifiedReduced.Setup.Proofs
