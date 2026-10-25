import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front136 from Data.GKRSetup.Unified.setupColumn7 start 17408 stop 17536

theorem frontLength136 : (front136.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front137 from Data.GKRSetup.Unified.setupColumn7 start 17536 stop 17664

theorem frontLength137 : (front137.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front138 from Data.GKRSetup.Unified.setupColumn7 start 17664 stop 17792

theorem frontLength138 : (front138.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front139 from Data.GKRSetup.Unified.setupColumn7 start 17792 stop 17920

theorem frontLength139 : (front139.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front140 from Data.GKRSetup.Unified.setupColumn7 start 17920 stop 18048

theorem frontLength140 : (front140.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front141 from Data.GKRSetup.Unified.setupColumn7 start 18048 stop 18176

theorem frontLength141 : (front141.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front142 from Data.GKRSetup.Unified.setupColumn7 start 18176 stop 18304

theorem frontLength142 : (front142.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part front143 from Data.GKRSetup.Unified.setupColumn7 start 18304 stop 18432

theorem frontLength143 : (front143.map Setup.Block.length).sum = 1216 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
