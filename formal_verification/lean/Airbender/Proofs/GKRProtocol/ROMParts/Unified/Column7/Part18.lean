import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front144 from Data.GKRSetup.Unified.setupColumn7 start 18432 stop 18560

theorem frontLength144 : (front144.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front145 from Data.GKRSetup.Unified.setupColumn7 start 18560 stop 18688

theorem frontLength145 : (front145.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front146 from Data.GKRSetup.Unified.setupColumn7 start 18688 stop 18816

theorem frontLength146 : (front146.map Setup.Block.length).sum = 1248 := by decide +kernel

column_blocks_part front147 from Data.GKRSetup.Unified.setupColumn7 start 18816 stop 18944

theorem frontLength147 : (front147.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front148 from Data.GKRSetup.Unified.setupColumn7 start 18944 stop 19072

theorem frontLength148 : (front148.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front149 from Data.GKRSetup.Unified.setupColumn7 start 19072 stop 19200

theorem frontLength149 : (front149.map Setup.Block.length).sum = 1096 := by decide +kernel

column_blocks_part front150 from Data.GKRSetup.Unified.setupColumn7 start 19200 stop 19328

theorem frontLength150 : (front150.map Setup.Block.length).sum = 1216 := by decide +kernel

column_blocks_part front151 from Data.GKRSetup.Unified.setupColumn7 start 19328 stop 19456

theorem frontLength151 : (front151.map Setup.Block.length).sum = 1232 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
