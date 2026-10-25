import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.ShiftBinop
import Airbender.Review.Helpers.Tables.ShiftData

namespace Airbender.Compiler.ShiftPrefixNative.Column9
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.ShiftBinop.setupColumn9
  start 0 stop 7
column_blocks_part target0Region0 from (Verification.byteZeroData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.byteSignData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (Verification.byteXorData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region3 from (Verification.byteOrData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region4 from (Verification.byteAndData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region5 from (Verification.byteTruncateData.columns[(9 : Nat)]) start 0 stop 1
column_blocks_part target0Region6 from Verification.byteShiftColumn9 start 0 stop 1
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  exact congrArg normalizeSetupBlocks (show original0 = target0 from rfl)

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 524545 := by decide +kernel

end Airbender.Compiler.ShiftPrefixNative.Column9
