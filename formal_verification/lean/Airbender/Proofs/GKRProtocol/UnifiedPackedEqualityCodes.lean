import Airbender.Import.PackedSetupEmbed
import Airbender.Data.GKRSetup.Unified
import Airbender.Data.Setup.UnifiedReduced.Native.XorData
import Airbender.Data.Setup.UnifiedReduced.Native.OrData
import Airbender.Data.Setup.UnifiedReduced.Native.AndData

namespace Airbender.Compiler.UnifiedPackedEquality
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
-- One data declaration covers the complete 2,584-block fixed-column family.
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

import_setup_code_capture from "artifacts/setup/unified.json" [
  sourceCode := column 2 block_start 128 block_count 2584 packed_region 54,
  xorCode := region 52 column 2 block_start 111 block_count 788 packed_bytes 0,
  orCode := region 53 column 2 block_start 0 block_count 898 packed_bytes 0,
  andCode := region 54 column 2 block_start 0 block_count 898 packed_bytes 1]

def targetCode : List BlockCode := xorCode ++ orCode ++ andCode

/-- The row-count conclusions of the established public chunk declarations. -/
def lengthChecks : List LengthCheck := [
  ⟨0, 128, 2360⟩,
  ⟨128, 128, 2280⟩,
  ⟨256, 128, 14560⟩,
  ⟨384, 128, 4840⟩,
  ⟨512, 128, 1368⟩,
  ⟨640, 128, 15680⟩,
  ⟨768, 128, 24320⟩,
  ⟨896, 128, 2480⟩,
  ⟨1024, 128, 2224⟩,
  ⟨1152, 128, 14368⟩,
  ⟨1280, 128, 5080⟩,
  ⟨1408, 128, 1352⟩,
  ⟨1536, 128, 15200⟩,
  ⟨1664, 128, 24704⟩,
  ⟨1792, 128, 2600⟩,
  ⟨1920, 128, 2168⟩,
  ⟨2048, 128, 14176⟩,
  ⟨2176, 128, 5320⟩,
  ⟨2304, 128, 1336⟩,
  ⟨2432, 128, 14720⟩,
  ⟨2560, 24, 6144⟩]

end Airbender.Compiler.UnifiedPackedEquality
