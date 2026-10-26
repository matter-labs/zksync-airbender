import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified
import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData
import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData

namespace Airbender.Compiler.UnifiedEqualChunks.Column4
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part original145 from Data.GKRSetup.Unified.setupColumn4 start 18560 stop 18688
column_blocks_part target145Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 18560 stop 18688
noncomputable def target145 : List Setup.Block := target145Region6

theorem chunkSame145 : original145 = target145 := by rfl

theorem chunkLength145 : (original145.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original146 from Data.GKRSetup.Unified.setupColumn4 start 18688 stop 18816
column_blocks_part target146Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 18688 stop 18816
noncomputable def target146 : List Setup.Block := target146Region6

theorem chunkSame146 : original146 = target146 := by rfl

theorem chunkLength146 : (original146.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part original147 from Data.GKRSetup.Unified.setupColumn4 start 18816 stop 18944
column_blocks_part target147Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 18816 stop 18944
noncomputable def target147 : List Setup.Block := target147Region6

theorem chunkSame147 : original147 = target147 := by rfl

theorem chunkLength147 : (original147.map Setup.Block.length).sum = 1224 := by decide +kernel

column_blocks_part original148 from Data.GKRSetup.Unified.setupColumn4 start 18944 stop 19072
column_blocks_part target148Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 18944 stop 19072
noncomputable def target148 : List Setup.Block := target148Region6

theorem chunkSame148 : original148 = target148 := by rfl

theorem chunkLength148 : (original148.map Setup.Block.length).sum = 1088 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
