import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Data
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupSpans

namespace Airbender.Compiler.UnifiedFixedSpans.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

-- Import all fixed requests in one command. Cache each verified region.
set_option maxHeartbeats 4000000

import_setup_code_capture from "artifacts/setup/unified.json" [
  source0 := column 3 block_start 0 block_count 1 unpacked,
  target0_0 := region 0 column 3 block_start 0 block_count 1 packed_bytes 0,
  target0_1 := region 1 column 3 block_start 0 block_count 1 packed_bytes 0,
  target0_2 := region 2 column 3 block_start 0 block_count 1 packed_bytes 0,
  target0_3 := region 3 column 3 block_start 0 block_count 1 packed_bytes 0,
  target0_4 := region 5 column 3 block_start 0 block_count 1 packed_bytes 0,
  target0_5 := region 8 column 3 block_start 0 block_count 1 packed_bytes 0,
  target0_6 := region 9 column 3 block_start 0 block_count 1 packed_bytes 0]

def targets0 : List BlockCode := target0_0 ++ target0_1 ++ target0_2 ++ target0_3 ++ target0_4 ++ target0_5 ++ target0_6

def requests : List PackedSetupSpans.Request := [
  ⟨source0.get ⟨0, by decide +kernel⟩, targets0⟩]

end Airbender.Compiler.UnifiedFixedSpans.Column3
