import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column5
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front184 from Data.GKRSetup.Unified.setupColumn5 start 23552 stop 23680

theorem frontLength184 : (front184.map Setup.Block.length).sum = 1161 := by decide +kernel

column_blocks_part front185 from Data.GKRSetup.Unified.setupColumn5 start 23680 stop 23808

theorem frontLength185 : (front185.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front186 from Data.GKRSetup.Unified.setupColumn5 start 23808 stop 23936

theorem frontLength186 : (front186.map Setup.Block.length).sum = 1206 := by decide +kernel

column_blocks_part front187 from Data.GKRSetup.Unified.setupColumn5 start 23936 stop 24064

theorem frontLength187 : (front187.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front188 from Data.GKRSetup.Unified.setupColumn5 start 24064 stop 24192

theorem frontLength188 : (front188.map Setup.Block.length).sum = 1226 := by decide +kernel

column_blocks_part front189 from Data.GKRSetup.Unified.setupColumn5 start 24192 stop 24320

theorem frontLength189 : (front189.map Setup.Block.length).sum = 1072 := by decide +kernel

column_blocks_part front190 from Data.GKRSetup.Unified.setupColumn5 start 24320 stop 24448

theorem frontLength190 : (front190.map Setup.Block.length).sum = 1064 := by decide +kernel

column_blocks_part front191 from Data.GKRSetup.Unified.setupColumn5 start 24448 stop 24541

theorem frontLength191 : (front191.map Setup.Block.length).sum = 775 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column5
