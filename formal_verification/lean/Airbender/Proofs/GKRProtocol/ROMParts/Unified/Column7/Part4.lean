import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front32 from Data.GKRSetup.Unified.setupColumn7 start 4096 stop 4224

theorem frontLength32 : (front32.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front33 from Data.GKRSetup.Unified.setupColumn7 start 4224 stop 4352

theorem frontLength33 : (front33.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part front34 from Data.GKRSetup.Unified.setupColumn7 start 4352 stop 4480

theorem frontLength34 : (front34.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front35 from Data.GKRSetup.Unified.setupColumn7 start 4480 stop 4608

theorem frontLength35 : (front35.map Setup.Block.length).sum = 1056 := by decide +kernel

column_blocks_part front36 from Data.GKRSetup.Unified.setupColumn7 start 4608 stop 4736

theorem frontLength36 : (front36.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front37 from Data.GKRSetup.Unified.setupColumn7 start 4736 stop 4864

theorem frontLength37 : (front37.map Setup.Block.length).sum = 1200 := by decide +kernel

column_blocks_part front38 from Data.GKRSetup.Unified.setupColumn7 start 4864 stop 4992

theorem frontLength38 : (front38.map Setup.Block.length).sum = 1048 := by decide +kernel

column_blocks_part front39 from Data.GKRSetup.Unified.setupColumn7 start 4992 stop 5120

theorem frontLength39 : (front39.map Setup.Block.length).sum = 1056 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column7
