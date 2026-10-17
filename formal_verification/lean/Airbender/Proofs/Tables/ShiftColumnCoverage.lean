import Airbender.Proofs.Tables.ImportedBinaryRows
import Airbender.Proofs.Tables.ShiftOutputExtent3
import Airbender.Proofs.Tables.ShiftOutputExtent2
import Airbender.Proofs.Tables.ShiftOutputExtent1
import Airbender.Proofs.Tables.ShiftOutputExtent0
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Review.Helpers.Tables.ShiftData
import Airbender.Proofs.Tables.ImportedBlocks
import Mathlib.Tactic.FinCases

namespace Airbender.Verification.ShiftColumns
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem shift_coverage (lane : Fin 10) :
    ((byteShiftData.columns[lane]).blocks.toList.map Block.length).sum = 262144 := by
  fin_cases lane
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ShiftCertificate.output0_coverage
  · exact ShiftCertificate.output1_coverage
  · exact ShiftCertificate.output2_coverage
  · exact ShiftCertificate.output3_coverage
  · decide +kernel
  · decide +kernel

theorem binary_coverage (kind : Fin 4) (lane : Fin 10) :
    let data : TableData 10 := #v[byteXorData, byteOrData, byteAndData, byteTruncateData][kind]
    ((data.columns[lane]).blocks.toList.map Block.length).sum = 65536 := by
  fin_cases kind <;> fin_cases lane
  · decide +kernel
  · decide +kernel
  · exact BinaryColumns.coverage 0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact BinaryColumns.coverage 1
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact BinaryColumns.coverage 2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem native_cast (kind : Fin 7) (index : Fin (shiftData kind).length) :
    (shiftRegionRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((shiftData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (shiftData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro lane hLane
  simp [shiftRegionRow, TableData.row, offset, signedValue_cast]

end Airbender.Verification.ShiftColumns
