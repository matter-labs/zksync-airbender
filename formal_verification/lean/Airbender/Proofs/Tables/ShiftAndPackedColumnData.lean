import Airbender.Data.Tables.Shift.AndPackedBlocks

namespace Airbender.Verification.ShiftPackedCertificate
open Airbender.Setup
set_option warningAsError true

/-- The original source column has exactly the decoded packed blocks. -/
theorem source_binding : byteAndData.columns[2].blocks.toList =
    byteAndPackedBlocks.map PackedBlock.decode := by
  change (byteAndDataPackedColumn2.map PackedBlock.decode).toArray.toList =
    byteAndDataPackedColumn2.map PackedBlock.decode
  exact List.toList_toArray

theorem same_source_bytes : byteAndPackedBlocksSourceBytes = byteAndDataSourceBytes := rfl

end Airbender.Verification.ShiftPackedCertificate
