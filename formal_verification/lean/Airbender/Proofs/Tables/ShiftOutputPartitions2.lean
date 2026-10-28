import Airbender.Data.Tables.Shift.Column6
import Airbender.Proofs.Tables.BlockPartition

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0
column_block_part output2Blocks0 from byteShiftColumn6 depth 4 part 0
column_block_part output2Blocks1 from byteShiftColumn6 depth 4 part 1
column_block_part output2Blocks2 from byteShiftColumn6 depth 4 part 2
column_block_part output2Blocks3 from byteShiftColumn6 depth 4 part 3
column_block_part output2Blocks4 from byteShiftColumn6 depth 4 part 4
column_block_part output2Blocks5 from byteShiftColumn6 depth 4 part 5
column_block_part output2Blocks6 from byteShiftColumn6 depth 4 part 6
column_block_part output2Blocks7 from byteShiftColumn6 depth 4 part 7
column_block_part output2Blocks8 from byteShiftColumn6 depth 4 part 8
column_block_part output2Blocks9 from byteShiftColumn6 depth 4 part 9
column_block_part output2Blocks10 from byteShiftColumn6 depth 4 part 10
column_block_part output2Blocks11 from byteShiftColumn6 depth 4 part 11
column_block_part output2Blocks12 from byteShiftColumn6 depth 4 part 12
column_block_part output2Blocks13 from byteShiftColumn6 depth 4 part 13
column_block_part output2Blocks14 from byteShiftColumn6 depth 4 part 14
column_block_part output2Blocks15 from byteShiftColumn6 depth 4 part 15
end Airbender.Verification.ShiftCertificate
