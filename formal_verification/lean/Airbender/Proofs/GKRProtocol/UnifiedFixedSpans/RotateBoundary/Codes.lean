import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Data
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupSpans

namespace Airbender.Compiler.UnifiedFixedSpans.RotateBoundary
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

-- Read and verify all five fixed regions in one data command.
set_option maxHeartbeats 2000000

import_setup_code_capture from "artifacts/setup/unified.json" [
  sourceCode := column 1 block_start 14 block_count 1 unpacked,
  target0 := region 47 column 1 block_start 1 block_count 1 packed_bytes 0,
  target1 := region 47 column 1 block_start 2 block_count 1 packed_bytes 0,
  target2 := region 48 column 1 block_start 0 block_count 1 packed_bytes 0,
  target3 := region 48 column 1 block_start 1 block_count 1 packed_bytes 0,
  target4 := region 48 column 1 block_start 2 block_count 1 packed_bytes 0,
  target5 := region 49 column 1 block_start 0 block_count 1 packed_bytes 0,
  target6 := region 49 column 1 block_start 1 block_count 1 packed_bytes 0,
  target7 := region 49 column 1 block_start 2 block_count 1 packed_bytes 0,
  target8 := region 50 column 1 block_start 0 block_count 1 packed_bytes 0,
  target9 := region 50 column 1 block_start 1 block_count 1 packed_bytes 0,
  target10 := region 50 column 1 block_start 2 block_count 1 packed_bytes 0,
  target11 := region 51 column 1 block_start 0 block_count 1 packed_bytes 0]

def targetsCode : List BlockCode := target0 ++ target1 ++ target2 ++ target3 ++ target4 ++ target5 ++ target6 ++ target7 ++ target8 ++ target9 ++ target10 ++ target11

def requests : List PackedSetupSpans.Request := [⟨sourceCode.get ⟨0, by decide +kernel⟩, targetsCode⟩]

end Airbender.Compiler.UnifiedFixedSpans.RotateBoundary
