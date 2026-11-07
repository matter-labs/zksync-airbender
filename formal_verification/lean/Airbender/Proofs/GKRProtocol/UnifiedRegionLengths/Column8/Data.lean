import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column8.Chunk0.Part0
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupLengths

namespace Airbender.Compiler.UnifiedRegionLengths.Column8
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

-- Import only fixed target pieces that have no existing numeric view.
import_setup_code_capture from "artifacts/setup/unified.json" [
  extra0 := region 0 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra1 := region 1 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra2 := region 2 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra3 := region 3 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra4 := region 5 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra5 := region 8 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra6 := region 9 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra7 := region 47 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra8 := region 48 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra9 := region 49 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra10 := region 50 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra11 := region 51 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra12 := region 52 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra13 := region 53 column 8 block_start 0 block_count 1 packed_bytes 0,
  extra14 := region 54 column 8 block_start 0 block_count 1 packed_bytes 0]

noncomputable def view0 : List BlockCode := extra0
noncomputable def view1 : List BlockCode := extra1
noncomputable def view2 : List BlockCode := extra2
noncomputable def view3 : List BlockCode := extra3
noncomputable def view4 : List BlockCode := extra4
noncomputable def view5 : List BlockCode := extra5
noncomputable def view6 : List BlockCode := extra6
noncomputable def view7 : List BlockCode := extra7
noncomputable def view8 : List BlockCode := extra8
noncomputable def view9 : List BlockCode := extra9
noncomputable def view10 : List BlockCode := extra10
noncomputable def view11 : List BlockCode := extra11
noncomputable def view12 : List BlockCode := extra12
noncomputable def view13 : List BlockCode := extra13
noncomputable def view14 : List BlockCode := extra14

-- These views support kernel proofs. They do not need runtime compilation.
noncomputable def requests : List Request := [
  ⟨view0, 1⟩,
  ⟨view1, 131072⟩,
  ⟨view2, 65536⟩,
  ⟨view3, 256⟩,
  ⟨view4, 65536⟩,
  ⟨view5, 65536⟩,
  ⟨view6, 262144⟩,
  ⟨view7, 65536⟩,
  ⟨view8, 65536⟩,
  ⟨view9, 65536⟩,
  ⟨view10, 65536⟩,
  ⟨view11, 128⟩,
  ⟨view12, 65536⟩,
  ⟨view13, 65536⟩,
  ⟨view14, 65536⟩]

end Airbender.Compiler.UnifiedRegionLengths.Column8
