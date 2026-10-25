import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.SubwordMemory
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Compiler.SubwordPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original0 from Data.GKRSetup.SubwordMemory.setupColumn6 start 0 stop 1
column_blocks_part target0Region0 from (Verification.subwordZeroData.columns[(6 : Nat)]) start 0 stop 1
column_blocks_part target0Region1 from (Verification.storePlaceData.columns[(6 : Nat)]) start 0 stop 1
column_blocks_part target0Region2 from (Verification.storeClearData.columns[(6 : Nat)]) start 0 stop 1
column_blocks_part target0Region3 from (Verification.loadHalfData.columns[(6 : Nat)]) start 0 stop 1
column_blocks_part target0Region4 from (Verification.loadByteData.columns[(6 : Nat)]) start 0 stop 1
column_blocks_part target0Region5 from (Verification.subwordROMHalfData.columns[(6 : Nat)]) start 0 stop 1
column_blocks_part target0Region6 from (Verification.subwordROMByteData.columns[(6 : Nat)]) start 0 stop 1
noncomputable def target0 : List Setup.Block := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rfl

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 13238273 := by decide +kernel

end Airbender.Compiler.SubwordPrefixNative.Column6
