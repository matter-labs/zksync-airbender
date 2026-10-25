import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front16 from Data.GKRSetup.Unified.setupColumn6 start 2048 stop 2176

theorem frontLength16 : (front16.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part front17 from Data.GKRSetup.Unified.setupColumn6 start 2176 stop 2304

theorem frontLength17 : (front17.map Setup.Block.length).sum = 1280 := by decide +kernel

column_blocks_part front18 from Data.GKRSetup.Unified.setupColumn6 start 2304 stop 2432

theorem frontLength18 : (front18.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part front19 from Data.GKRSetup.Unified.setupColumn6 start 2432 stop 2560

theorem frontLength19 : (front19.map Setup.Block.length).sum = 1264 := by decide +kernel

column_blocks_part front20 from Data.GKRSetup.Unified.setupColumn6 start 2560 stop 2688

theorem frontLength20 : (front20.map Setup.Block.length).sum = 1288 := by decide +kernel

column_blocks_part front21 from Data.GKRSetup.Unified.setupColumn6 start 2688 stop 2816

theorem frontLength21 : (front21.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part front22 from Data.GKRSetup.Unified.setupColumn6 start 2816 stop 2944

theorem frontLength22 : (front22.map Setup.Block.length).sum = 1272 := by decide +kernel

column_blocks_part front23 from Data.GKRSetup.Unified.setupColumn6 start 2944 stop 3072

theorem frontLength23 : (front23.map Setup.Block.length).sum = 1112 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
