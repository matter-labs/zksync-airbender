import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front40 from Data.GKRSetup.Unified.setupColumn7 start 5120 stop 5248

theorem frontLength40 : (front40.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front41 from Data.GKRSetup.Unified.setupColumn7 start 5248 stop 5376

theorem frontLength41 : (front41.map Setup.Block.length).sum = 1208 := by decide +kernel

column_blocks_part front42 from Data.GKRSetup.Unified.setupColumn7 start 5376 stop 5504

theorem frontLength42 : (front42.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front43 from Data.GKRSetup.Unified.setupColumn7 start 5504 stop 5632

theorem frontLength43 : (front43.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part front44 from Data.GKRSetup.Unified.setupColumn7 start 5632 stop 5760

theorem frontLength44 : (front44.map Setup.Block.length).sum = 1208 := by decide +kernel

column_blocks_part front45 from Data.GKRSetup.Unified.setupColumn7 start 5760 stop 5888

theorem frontLength45 : (front45.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front46 from Data.GKRSetup.Unified.setupColumn7 start 5888 stop 6016

theorem frontLength46 : (front46.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part front47 from Data.GKRSetup.Unified.setupColumn7 start 6016 stop 6144

theorem frontLength47 : (front47.map Setup.Block.length).sum = 1048 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
