import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original65 from Data.GKRSetup.Unified.setupColumn6 start 8320 stop 8448
column_blocks_part target65Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 8320 stop 8448
noncomputable def target65 : List Setup.Block := target65Region6

theorem chunkSame65 : original65 = target65 := by rfl

theorem chunkLength65 : (original65.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part original66 from Data.GKRSetup.Unified.setupColumn6 start 8448 stop 8576
column_blocks_part target66Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 8448 stop 8576
noncomputable def target66 : List Setup.Block := target66Region6

theorem chunkSame66 : original66 = target66 := by rfl

theorem chunkLength66 : (original66.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part original67 from Data.GKRSetup.Unified.setupColumn6 start 8576 stop 8704
column_blocks_part target67Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 8576 stop 8704
noncomputable def target67 : List Setup.Block := target67Region6

theorem chunkSame67 : original67 = target67 := by rfl

theorem chunkLength67 : (original67.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part original68 from Data.GKRSetup.Unified.setupColumn6 start 8704 stop 8832
column_blocks_part target68Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 8704 stop 8832
noncomputable def target68 : List Setup.Block := target68Region6

theorem chunkSame68 : original68 = target68 := by rfl

theorem chunkLength68 : (original68.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
