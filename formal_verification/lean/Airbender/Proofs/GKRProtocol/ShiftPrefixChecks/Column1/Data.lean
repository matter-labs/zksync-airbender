import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Data.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
-- This command group names the complete imported column data.
set_option maxHeartbeats 4000000

column_blocks_part original0 from Data.GKRSetup.ShiftBinop.setupColumn1
  start 0 stop 7
column_blocks_part target0Region0 from (Verification.byteZeroData.columns[(1 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.byteSignData.columns[(1 : Nat)]) start 0 stop 2
column_blocks_part target0Region2 from (Verification.byteXorData.columns[(1 : Nat)]) start 0 stop 1
column_blocks_part target0Region3 from (Verification.byteOrData.columns[(1 : Nat)]) start 0 stop 1
column_blocks_part target0Region4 from (Verification.byteAndData.columns[(1 : Nat)]) start 0 stop 1
column_blocks_part target0Region5 from (Verification.byteTruncateData.columns[(1 : Nat)]) start 0 stop 1
column_blocks_part target0Region6 from Verification.byteShiftColumn1 start 0 stop 4
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6

end Airbender.Compiler.ShiftPrefixNative.Column1
