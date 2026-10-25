import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original149 from Data.GKRSetup.Unified.setupColumn4 start 19072 stop 19200
column_blocks_part target149Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 19072 stop 19200
noncomputable def target149 : List Setup.Block := target149Region6

theorem chunkSame149 : original149 = target149 := by rfl

theorem chunkLength149 : (original149.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part original150 from Data.GKRSetup.Unified.setupColumn4 start 19200 stop 19328
column_blocks_part target150Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 19200 stop 19328
noncomputable def target150 : List Setup.Block := target150Region6

theorem chunkSame150 : original150 = target150 := by rfl

theorem chunkLength150 : (original150.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part original151 from Data.GKRSetup.Unified.setupColumn4 start 19328 stop 19456
column_blocks_part target151Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 19328 stop 19456
noncomputable def target151 : List Setup.Block := target151Region6

theorem chunkSame151 : original151 = target151 := by rfl

theorem chunkLength151 : (original151.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original152 from Data.GKRSetup.Unified.setupColumn4 start 19456 stop 19584
column_blocks_part target152Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 19456 stop 19584
noncomputable def target152 : List Setup.Block := target152Region6

theorem chunkSame152 : original152 = target152 := by rfl

theorem chunkLength152 : (original152.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
