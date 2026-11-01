import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupLengths

namespace Airbender.Compiler.SubwordRegionLengths.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false

-- Import only the five fixed target regions.
import_setup_code_capture from "artifacts/setup/subword-memory.json" [
  region0 := region 0 column 3 block_start 0 block_count 1 packed_bytes 0,
  region1 := region 29 column 3 block_start 0 block_count 1 packed_bytes 0,
  region2 := region 30 column 3 block_start 0 block_count 1 packed_bytes 0,
  region3 := region 42 column 3 block_start 0 block_count 1 packed_bytes 0,
  region4 := region 43 column 3 block_start 0 block_count 1 packed_bytes 0]

noncomputable def requests : List Request := [
  ⟨region0, 1⟩,
  ⟨region1, 131072⟩,
  ⟨region2, 131072⟩,
  ⟨region3, 131072⟩,
  ⟨region4, 262144⟩]

end Airbender.Compiler.SubwordRegionLengths.Column3
