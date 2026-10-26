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

column_blocks_part original97 from Data.GKRSetup.Unified.setupColumn4 start 12416 stop 12544
column_blocks_part target97Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 12416 stop 12544
noncomputable def target97 : List Setup.Block := target97Region6

theorem chunkSame97 : original97 = target97 := by rfl

theorem chunkLength97 : (original97.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original98 from Data.GKRSetup.Unified.setupColumn4 start 12544 stop 12672
column_blocks_part target98Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 12544 stop 12672
noncomputable def target98 : List Setup.Block := target98Region6

theorem chunkSame98 : original98 = target98 := by rfl

theorem chunkLength98 : (original98.map Setup.Block.length).sum = 1272 := by decide +kernel

column_blocks_part original99 from Data.GKRSetup.Unified.setupColumn4 start 12672 stop 12800
column_blocks_part target99Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 12672 stop 12800
noncomputable def target99 : List Setup.Block := target99Region6

theorem chunkSame99 : original99 = target99 := by rfl

theorem chunkLength99 : (original99.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part original100 from Data.GKRSetup.Unified.setupColumn4 start 12800 stop 12928
column_blocks_part target100Region6 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 12800 stop 12928
noncomputable def target100 : List Setup.Block := target100Region6

theorem chunkSame100 : original100 = target100 := by rfl

theorem chunkLength100 : (original100.map Setup.Block.length).sum = 1296 := by decide +kernel

end Airbender.Compiler.UnifiedEqualChunks.Column4
