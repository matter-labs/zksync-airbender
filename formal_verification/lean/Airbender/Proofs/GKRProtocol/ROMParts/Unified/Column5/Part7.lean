import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front56 from Data.GKRSetup.Unified.setupColumn5 start 7168 stop 7296

theorem frontLength56 : (front56.map Setup.Block.length).sum = 2304 := by decide +kernel

column_blocks_part front57 from Data.GKRSetup.Unified.setupColumn5 start 7296 stop 7424

theorem frontLength57 : (front57.map Setup.Block.length).sum = 2094 := by decide +kernel

column_blocks_part front58 from Data.GKRSetup.Unified.setupColumn5 start 7424 stop 7552

theorem frontLength58 : (front58.map Setup.Block.length).sum = 2290 := by decide +kernel

column_blocks_part front59 from Data.GKRSetup.Unified.setupColumn5 start 7552 stop 7680

theorem frontLength59 : (front59.map Setup.Block.length).sum = 2280 := by decide +kernel

column_blocks_part front60 from Data.GKRSetup.Unified.setupColumn5 start 7680 stop 7808

theorem frontLength60 : (front60.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part front61 from Data.GKRSetup.Unified.setupColumn5 start 7808 stop 7936

theorem frontLength61 : (front61.map Setup.Block.length).sum = 2272 := by decide +kernel

column_blocks_part front62 from Data.GKRSetup.Unified.setupColumn5 start 7936 stop 8064

theorem frontLength62 : (front62.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part front63 from Data.GKRSetup.Unified.setupColumn5 start 8064 stop 8192

theorem frontLength63 : (front63.map Setup.Block.length).sum = 2280 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column5
