import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original125 from Data.GKRSetup.Unified.setupColumn7 start 16000 stop 16128
column_blocks_part target125Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16000 stop 16128
noncomputable def target125 : List Setup.Block := target125Region6

theorem chunkSame125 : original125 = target125 := by rfl

theorem chunkLength125 : (original125.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original126 from Data.GKRSetup.Unified.setupColumn7 start 16128 stop 16256
column_blocks_part target126Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16128 stop 16256
noncomputable def target126 : List Setup.Block := target126Region6

theorem chunkSame126 : original126 = target126 := by rfl

theorem chunkLength126 : (original126.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part original127 from Data.GKRSetup.Unified.setupColumn7 start 16256 stop 16384
column_blocks_part target127Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16256 stop 16384
noncomputable def target127 : List Setup.Block := target127Region6

theorem chunkSame127 : original127 = target127 := by rfl

theorem chunkLength127 : (original127.map Setup.Block.length).sum = 1120 := by decide +kernel

column_blocks_part original128 from Data.GKRSetup.Unified.setupColumn7 start 16384 stop 16512
column_blocks_part target128Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 16384 stop 16512
noncomputable def target128 : List Setup.Block := target128Region6

theorem chunkSame128 : original128 = target128 := by rfl

theorem chunkLength128 : (original128.map Setup.Block.length).sum = 1256 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column7
