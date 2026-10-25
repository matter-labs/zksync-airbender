import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front8 from Data.GKRSetup.Unified.setupColumn6 start 1024 stop 1152

theorem frontLength8 : (front8.map Setup.Block.length).sum = 1480 := by decide +kernel

column_blocks_part front9 from Data.GKRSetup.Unified.setupColumn6 start 1152 stop 1280

theorem frontLength9 : (front9.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part front10 from Data.GKRSetup.Unified.setupColumn6 start 1280 stop 1408

theorem frontLength10 : (front10.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part front11 from Data.GKRSetup.Unified.setupColumn6 start 1408 stop 1536

theorem frontLength11 : (front11.map Setup.Block.length).sum = 1448 := by decide +kernel

column_blocks_part front12 from Data.GKRSetup.Unified.setupColumn6 start 1536 stop 1664

theorem frontLength12 : (front12.map Setup.Block.length).sum = 1120 := by decide +kernel

column_blocks_part front13 from Data.GKRSetup.Unified.setupColumn6 start 1664 stop 1792

theorem frontLength13 : (front13.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part front14 from Data.GKRSetup.Unified.setupColumn6 start 1792 stop 1920

theorem frontLength14 : (front14.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part front15 from Data.GKRSetup.Unified.setupColumn6 start 1920 stop 2048

theorem frontLength15 : (front15.map Setup.Block.length).sum = 1256 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
