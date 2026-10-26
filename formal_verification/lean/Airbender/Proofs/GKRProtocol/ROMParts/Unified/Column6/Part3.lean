import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front24 from Data.GKRSetup.Unified.setupColumn6 start 3072 stop 3200

theorem frontLength24 : (front24.map Setup.Block.length).sum = 1256 := by decide +kernel

column_blocks_part front25 from Data.GKRSetup.Unified.setupColumn6 start 3200 stop 3328

theorem frontLength25 : (front25.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front26 from Data.GKRSetup.Unified.setupColumn6 start 3328 stop 3456

theorem frontLength26 : (front26.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front27 from Data.GKRSetup.Unified.setupColumn6 start 3456 stop 3584

theorem frontLength27 : (front27.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front28 from Data.GKRSetup.Unified.setupColumn6 start 3584 stop 3712

theorem frontLength28 : (front28.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front29 from Data.GKRSetup.Unified.setupColumn6 start 3712 stop 3840

theorem frontLength29 : (front29.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front30 from Data.GKRSetup.Unified.setupColumn6 start 3840 stop 3968

theorem frontLength30 : (front30.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front31 from Data.GKRSetup.Unified.setupColumn6 start 3968 stop 4096

theorem frontLength31 : (front31.map Setup.Block.length).sum = 1240 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
