import Airbender.Proofs.Tables.ShiftAndPackedColumnData
import Airbender.Proofs.Tables.PackedBlockCertificate

namespace Airbender.Verification.ShiftPackedCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
-- The kernel checks all 898 packed source blocks in one Boolean fact.
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def check (capture : List PackedBlock) : Bool :=
  (capture.map PackedBlock.length).sum == 65536 && PackedBlockCertificate.check 0 capture

theorem ok : check byteAndPackedBlocks = true := by decide +kernel

theorem check_sound (capture : List PackedBlock) (checked : check capture = true) :
    checkBlocks (fun n => n / 256 &&& n % 256) 0 (capture.map PackedBlock.decode) = true :=
  PackedBlockCertificate.check_sound 0 capture (by
    simp only [check, Bool.and_eq_true] at checked
    exact checked.2)

theorem coverage :
    (byteAndData.columns[2].blocks.toList.map Block.length).sum = 65536 := by
  rw [source_binding]
  have checked := ok
  simp only [check, Bool.and_eq_true, beq_iff_eq] at checked
  simpa only [List.map_map, Function.comp_def, PackedBlockCertificate.decode_length] using checked.1

/-- This is exactly the established raw-column result. -/
theorem and_outputs :
    checkBlocks (fun n => n / 256 &&& n % 256) 0
      byteAndData.columns[2].blocks.toList = true := by
  rw [source_binding]
  exact check_sound _ ok

end Airbender.Verification.ShiftPackedCertificate
