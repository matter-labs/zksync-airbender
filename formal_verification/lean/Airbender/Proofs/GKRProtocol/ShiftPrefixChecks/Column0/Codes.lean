import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column0.Data
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupNormalization

namespace Airbender.Compiler.ShiftPrefixChecks.Column0
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupNormalization
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

-- The importer reads the complete capture once. Each leaf has at most 128 blocks.
set_option maxHeartbeats 4000000

import_setup_code_capture from "artifacts/setup/shift-binop.json" [
  source0 := column 0 block_start 0 block_count 10 unpacked,
  target0Region0 := region 0 column 0 block_start 0 block_count 1 packed_bytes 0,
  target0Region1 := region 3 column 0 block_start 0 block_count 1 packed_bytes 0,
  target0Region2 := region 4 column 0 block_start 0 block_count 1 packed_bytes 0,
  target0Region3 := region 6 column 0 block_start 0 block_count 1 packed_bytes 0,
  target0Region4 := region 7 column 0 block_start 0 block_count 1 packed_bytes 0,
  target0Region5 := region 8 column 0 block_start 0 block_count 1 packed_bytes 0,
  target0Region6 := region 9 column 0 block_start 0 block_count 4 packed_bytes 0]

def requests : List Request := [
  ⟨source0, target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6, 524545⟩,
  ⟨target0Region0, target0Region0, 1⟩,
  ⟨target0Region1, target0Region1, 256⟩,
  ⟨target0Region2, target0Region2, 65536⟩,
  ⟨target0Region3, target0Region3, 65536⟩,
  ⟨target0Region4, target0Region4, 65536⟩,
  ⟨target0Region5, target0Region5, 65536⟩,
  ⟨target0Region6, target0Region6, 262144⟩]

end Airbender.Compiler.ShiftPrefixChecks.Column0
