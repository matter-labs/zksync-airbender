import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front64 from Data.GKRSetup.Unified.setupColumn5 start 8192 stop 8320

theorem frontLength64 : (front64.map Setup.Block.length).sum = 2080 := by decide +kernel

column_blocks_part front65 from Data.GKRSetup.Unified.setupColumn5 start 8320 stop 8448

theorem frontLength65 : (front65.map Setup.Block.length).sum = 2272 := by decide +kernel

column_blocks_part front66 from Data.GKRSetup.Unified.setupColumn5 start 8448 stop 8576

theorem frontLength66 : (front66.map Setup.Block.length).sum = 2072 := by decide +kernel

column_blocks_part front67 from Data.GKRSetup.Unified.setupColumn5 start 8576 stop 8704

theorem frontLength67 : (front67.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front68 from Data.GKRSetup.Unified.setupColumn5 start 8704 stop 8832

theorem frontLength68 : (front68.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front69 from Data.GKRSetup.Unified.setupColumn5 start 8832 stop 8960

theorem frontLength69 : (front69.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front70 from Data.GKRSetup.Unified.setupColumn5 start 8960 stop 9088

theorem frontLength70 : (front70.map Setup.Block.length).sum = 2048 := by decide +kernel

column_blocks_part front71 from Data.GKRSetup.Unified.setupColumn5 start 9088 stop 9216

theorem frontLength71 : (front71.map Setup.Block.length).sum = 2048 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column5
