import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original93 from Data.GKRSetup.Unified.setupColumn5 start 11904 stop 12032
column_blocks_part target93Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 11904 stop 12032
noncomputable def target93 : List Setup.Block := target93Region6

theorem chunkSame93 : original93 = target93 := by rfl

theorem chunkLength93 : (original93.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original94 from Data.GKRSetup.Unified.setupColumn5 start 12032 stop 12160
column_blocks_part target94Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 12032 stop 12160
noncomputable def target94 : List Setup.Block := target94Region6

theorem chunkSame94 : original94 = target94 := by rfl

theorem chunkLength94 : (original94.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original95 from Data.GKRSetup.Unified.setupColumn5 start 12160 stop 12288
column_blocks_part target95Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 12160 stop 12288
noncomputable def target95 : List Setup.Block := target95Region6

theorem chunkSame95 : original95 = target95 := by rfl

theorem chunkLength95 : (original95.map Setup.Block.length).sum = 1224 := by decide +kernel

column_blocks_part original96 from Data.GKRSetup.Unified.setupColumn5 start 12288 stop 12416
column_blocks_part target96Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 12288 stop 12416
noncomputable def target96 : List Setup.Block := target96Region6

theorem chunkSame96 : original96 = target96 := by rfl

theorem chunkLength96 : (original96.map Setup.Block.length).sum = 1088 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column5
