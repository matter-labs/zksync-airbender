import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front152 from Data.GKRSetup.Unified.setupColumn7 start 19456 stop 19584

theorem frontLength152 : (front152.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front153 from Data.GKRSetup.Unified.setupColumn7 start 19584 stop 19712

theorem frontLength153 : (front153.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front154 from Data.GKRSetup.Unified.setupColumn7 start 19712 stop 19840

theorem frontLength154 : (front154.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front155 from Data.GKRSetup.Unified.setupColumn7 start 19840 stop 19968

theorem frontLength155 : (front155.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front156 from Data.GKRSetup.Unified.setupColumn7 start 19968 stop 20096

theorem frontLength156 : (front156.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part front157 from Data.GKRSetup.Unified.setupColumn7 start 20096 stop 20224

theorem frontLength157 : (front157.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part front158 from Data.GKRSetup.Unified.setupColumn7 start 20224 stop 20352

theorem frontLength158 : (front158.map Setup.Block.length).sum = 1088 := by decide +kernel

column_blocks_part front159 from Data.GKRSetup.Unified.setupColumn7 start 20352 stop 20480

theorem frontLength159 : (front159.map Setup.Block.length).sum = 1224 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
