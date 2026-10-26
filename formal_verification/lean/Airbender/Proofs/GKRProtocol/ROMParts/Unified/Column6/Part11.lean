import Airbender.Import.GKRProtocol.BlockPartsImport
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part front88 from Data.GKRSetup.Unified.setupColumn6 start 11264 stop 11392

theorem frontLength88 : (front88.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front89 from Data.GKRSetup.Unified.setupColumn6 start 11392 stop 11520

theorem frontLength89 : (front89.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front90 from Data.GKRSetup.Unified.setupColumn6 start 11520 stop 11648

theorem frontLength90 : (front90.map Setup.Block.length).sum = 1232 := by decide +kernel

column_blocks_part front91 from Data.GKRSetup.Unified.setupColumn6 start 11648 stop 11776

theorem frontLength91 : (front91.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front92 from Data.GKRSetup.Unified.setupColumn6 start 11776 stop 11904

theorem frontLength92 : (front92.map Setup.Block.length).sum = 1248 := by decide +kernel

column_blocks_part front93 from Data.GKRSetup.Unified.setupColumn6 start 11904 stop 12032

theorem frontLength93 : (front93.map Setup.Block.length).sum = 1240 := by decide +kernel

column_blocks_part front94 from Data.GKRSetup.Unified.setupColumn6 start 12032 stop 12160

theorem frontLength94 : (front94.map Setup.Block.length).sum = 1080 := by decide +kernel

column_blocks_part front95 from Data.GKRSetup.Unified.setupColumn6 start 12160 stop 12288

theorem frontLength95 : (front95.map Setup.Block.length).sum = 1232 := by decide +kernel

end Airbender.Compiler.ROMColumns.Unified.Column6
