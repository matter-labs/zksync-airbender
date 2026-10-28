import Airbender.Data.Tables.Shift.Column7
import Airbender.Proofs.Tables.BlockPartition

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0
column_block_part output3Blocks0 from byteShiftColumn7 depth 4 part 0
column_block_part output3Blocks1 from byteShiftColumn7 depth 4 part 1
column_block_part output3Blocks2 from byteShiftColumn7 depth 4 part 2
column_block_part output3Blocks3 from byteShiftColumn7 depth 4 part 3
column_block_part output3Blocks4 from byteShiftColumn7 depth 4 part 4
column_block_part output3Blocks5 from byteShiftColumn7 depth 4 part 5
column_block_part output3Blocks6 from byteShiftColumn7 depth 4 part 6
column_block_part output3Blocks7 from byteShiftColumn7 depth 4 part 7
column_block_part output3Blocks8 from byteShiftColumn7 depth 4 part 8
column_block_part output3Blocks9 from byteShiftColumn7 depth 4 part 9
column_block_part output3Blocks10 from byteShiftColumn7 depth 4 part 10
column_block_part output3Blocks11 from byteShiftColumn7 depth 4 part 11
column_block_part output3Blocks12 from byteShiftColumn7 depth 4 part 12
column_block_part output3Blocks13 from byteShiftColumn7 depth 4 part 13
column_block_part output3Blocks14 from byteShiftColumn7 depth 4 part 14
column_block_part output3Blocks15 from byteShiftColumn7 depth 4 part 15
end Airbender.Verification.ShiftCertificate
