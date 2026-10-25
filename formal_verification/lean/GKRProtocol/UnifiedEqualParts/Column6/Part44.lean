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

column_blocks_part original177 from Data.GKRSetup.Unified.setupColumn6 start 22656 stop 22784
column_blocks_part target177Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22656 stop 22784
noncomputable def target177 : List Setup.Block := target177Region6

theorem chunkSame177 : original177 = target177 := by rfl

theorem chunkLength177 : (original177.map Setup.Block.length).sum = 1089 := by decide +kernel

column_blocks_part original178 from Data.GKRSetup.Unified.setupColumn6 start 22784 stop 22912
column_blocks_part target178Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22784 stop 22912
noncomputable def target178 : List Setup.Block := target178Region6

theorem chunkSame178 : original178 = target178 := by rfl

theorem chunkLength178 : (original178.map Setup.Block.length).sum = 1079 := by decide +kernel

column_blocks_part original179 from Data.GKRSetup.Unified.setupColumn6 start 22912 stop 23040
column_blocks_part target179Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 22912 stop 23040
noncomputable def target179 : List Setup.Block := target179Region6

theorem chunkSame179 : original179 = target179 := by rfl

theorem chunkLength179 : (original179.map Setup.Block.length).sum = 1199 := by decide +kernel

column_blocks_part original180 from Data.GKRSetup.Unified.setupColumn6 start 23040 stop 23168
column_blocks_part target180Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 23040 stop 23168
noncomputable def target180 : List Setup.Block := target180Region6

theorem chunkSame180 : original180 = target180 := by rfl

theorem chunkLength180 : (original180.map Setup.Block.length).sum = 1072 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column6
