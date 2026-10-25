import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front176 from Data.GKRSetup.Unified.setupColumn6 start 22528 stop 22656

theorem frontLength176 : (front176.map Setup.Block.length).sum = 1193 := by decide +kernel

column_blocks_part front177 from Data.GKRSetup.Unified.setupColumn6 start 22656 stop 22784

theorem frontLength177 : (front177.map Setup.Block.length).sum = 1089 := by decide +kernel

column_blocks_part front178 from Data.GKRSetup.Unified.setupColumn6 start 22784 stop 22912

theorem frontLength178 : (front178.map Setup.Block.length).sum = 1079 := by decide +kernel

column_blocks_part front179 from Data.GKRSetup.Unified.setupColumn6 start 22912 stop 23040

theorem frontLength179 : (front179.map Setup.Block.length).sum = 1199 := by decide +kernel

column_blocks_part front180 from Data.GKRSetup.Unified.setupColumn6 start 23040 stop 23168

theorem frontLength180 : (front180.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part front181 from Data.GKRSetup.Unified.setupColumn6 start 23168 stop 23296

theorem frontLength181 : (front181.map Setup.Block.length).sum = 1193 := by decide +kernel

column_blocks_part front182 from Data.GKRSetup.Unified.setupColumn6 start 23296 stop 23424

theorem frontLength182 : (front182.map Setup.Block.length).sum = 1097 := by decide +kernel

column_blocks_part front183 from Data.GKRSetup.Unified.setupColumn6 start 23424 stop 23552

theorem frontLength183 : (front183.map Setup.Block.length).sum = 1064 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
