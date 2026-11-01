import Airbender.Proofs.Tables.ShiftPackedEncoding.Column0Data
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column0Reference

namespace Airbender.Verification.ShiftPackedEncoding.Lane0
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks PackedWordColumn
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : column.check = true := by decide +kernel

theorem native_get (index : Nat) (within : index < 262144) :
    getFromBlocks byteShiftColumn4.blocks.toList index =
      some (PackedSignedRun.digit 65536 column.payload index) := by
  have result := (column.check_sound checked).2.2 index (by simpa only [row_count] using within)
  rw [column_blocks, source_binding] at result
  exact result

theorem reference_checked : column.checkLeaves (ShiftPackedReference.checkSpan 0) 0 = true := by
  rw [column.checkLeaves_requests, requests_binding]
  exact requests_checked

theorem native_checks : checkBlocks (ShiftCertificate.outputByte 0) 0
    byteShiftColumn4.blocks.toList = true := by
  rw [ShiftCertificate.outputByte_normalized]
  have result := column.checkLeaves_sound (ShiftCertificate.outputNatByte 0)
    (ShiftPackedReference.checkSpan 0)
    (ShiftPackedReference.checkSpan_sound 0 (by decide +kernel)) 0 checked reference_checked
  rw [column_blocks, source_binding] at result
  exact result

end Airbender.Verification.ShiftPackedEncoding.Lane0
