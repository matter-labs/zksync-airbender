import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front96 from Data.GKRSetup.Unified.setupColumn7 start 12288 stop 12416

theorem frontLength96 : (front96.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front97 from Data.GKRSetup.Unified.setupColumn7 start 12416 stop 12544

theorem frontLength97 : (front97.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front98 from Data.GKRSetup.Unified.setupColumn7 start 12544 stop 12672

theorem frontLength98 : (front98.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front99 from Data.GKRSetup.Unified.setupColumn7 start 12672 stop 12800

theorem frontLength99 : (front99.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front100 from Data.GKRSetup.Unified.setupColumn7 start 12800 stop 12928

theorem frontLength100 : (front100.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front101 from Data.GKRSetup.Unified.setupColumn7 start 12928 stop 13056

theorem frontLength101 : (front101.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front102 from Data.GKRSetup.Unified.setupColumn7 start 13056 stop 13184

theorem frontLength102 : (front102.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front103 from Data.GKRSetup.Unified.setupColumn7 start 13184 stop 13312

theorem frontLength103 : (front103.map Setup.Block.length).sum = 1080 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
