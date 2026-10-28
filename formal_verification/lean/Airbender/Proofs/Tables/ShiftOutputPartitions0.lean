import Airbender.Data.Tables.Shift.Column4
import Airbender.Proofs.Tables.BlockPartition

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0
column_block_part output0Blocks0 from byteShiftColumn4 depth 4 part 0
column_block_part output0Blocks1 from byteShiftColumn4 depth 4 part 1
column_block_part output0Blocks2 from byteShiftColumn4 depth 4 part 2
column_block_part output0Blocks3 from byteShiftColumn4 depth 4 part 3
column_block_part output0Blocks4 from byteShiftColumn4 depth 4 part 4
column_block_part output0Blocks5 from byteShiftColumn4 depth 4 part 5
column_block_part output0Blocks6 from byteShiftColumn4 depth 4 part 6
column_block_part output0Blocks7 from byteShiftColumn4 depth 4 part 7
column_block_part output0Blocks8 from byteShiftColumn4 depth 4 part 8
column_block_part output0Blocks9 from byteShiftColumn4 depth 4 part 9
column_block_part output0Blocks10 from byteShiftColumn4 depth 4 part 10
column_block_part output0Blocks11 from byteShiftColumn4 depth 4 part 11
column_block_part output0Blocks12 from byteShiftColumn4 depth 4 part 12
column_block_part output0Blocks13 from byteShiftColumn4 depth 4 part 13
column_block_part output0Blocks14 from byteShiftColumn4 depth 4 part 14
column_block_part output0Blocks15 from byteShiftColumn4 depth 4 part 15
end Airbender.Verification.ShiftCertificate
