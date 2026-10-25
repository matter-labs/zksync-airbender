import GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front0 from Data.GKRSetup.Unified.setupColumn6 start 0 stop 128

theorem frontLength0 : (front0.map Setup.Block.length).sum = 330099 := by decide +kernel

column_blocks_part front1 from Data.GKRSetup.Unified.setupColumn6 start 128 stop 256

theorem frontLength1 : (front1.map Setup.Block.length).sum = 1568 := by decide +kernel

column_blocks_part front2 from Data.GKRSetup.Unified.setupColumn6 start 256 stop 384

theorem frontLength2 : (front2.map Setup.Block.length).sum = 1528 := by decide +kernel

column_blocks_part front3 from Data.GKRSetup.Unified.setupColumn6 start 384 stop 512

theorem frontLength3 : (front3.map Setup.Block.length).sum = 1520 := by decide +kernel

column_blocks_part front4 from Data.GKRSetup.Unified.setupColumn6 start 512 stop 640

theorem frontLength4 : (front4.map Setup.Block.length).sum = 1344 := by decide +kernel

column_blocks_part front5 from Data.GKRSetup.Unified.setupColumn6 start 640 stop 768

theorem frontLength5 : (front5.map Setup.Block.length).sum = 1488 := by decide +kernel

column_blocks_part front6 from Data.GKRSetup.Unified.setupColumn6 start 768 stop 896

theorem frontLength6 : (front6.map Setup.Block.length).sum = 1304 := by decide +kernel

column_blocks_part front7 from Data.GKRSetup.Unified.setupColumn6 start 896 stop 1024

theorem frontLength7 : (front7.map Setup.Block.length).sum = 1304 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
