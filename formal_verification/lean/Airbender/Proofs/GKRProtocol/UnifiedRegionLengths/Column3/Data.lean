import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Bindings
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupLengths

namespace Airbender.Compiler.UnifiedRegionLengths.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

-- Import only fixed target pieces that have no existing numeric view.
import_setup_code_capture from "artifacts/setup/unified.json" [
  extra7 := region 9 column 3 block_start 1 block_count 1 packed_bytes 0,
  extra8 := region 9 column 3 block_start 2 block_count 1 packed_bytes 0,
  extra9 := region 47 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra10 := region 48 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra11 := region 49 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra12 := region 50 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra13 := region 51 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra14 := region 52 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra15 := region 53 column 3 block_start 0 block_count 1 packed_bytes 0,
  extra16 := region 54 column 3 block_start 0 block_count 1 packed_bytes 0]

noncomputable def view0 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_0
noncomputable def view1 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_1
noncomputable def view2 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_2
noncomputable def view3 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_3
noncomputable def view4 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_4
noncomputable def view5 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_5
noncomputable def view6 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column3.target0_6
noncomputable def view7 : List BlockCode := extra7
noncomputable def view8 : List BlockCode := extra8
noncomputable def view9 : List BlockCode := extra9
noncomputable def view10 : List BlockCode := extra10
noncomputable def view11 : List BlockCode := extra11
noncomputable def view12 : List BlockCode := extra12
noncomputable def view13 : List BlockCode := extra13
noncomputable def view14 : List BlockCode := extra14
noncomputable def view15 : List BlockCode := extra15
noncomputable def view16 : List BlockCode := extra16

-- These views support kernel proofs. They do not need runtime compilation.
noncomputable def requests : List Request := [
  ⟨view0, 1⟩,
  ⟨view1, 131072⟩,
  ⟨view2, 65536⟩,
  ⟨view3, 256⟩,
  ⟨view4, 65536⟩,
  ⟨view5, 65536⟩,
  ⟨view6, 1⟩,
  ⟨view7, 262136⟩,
  ⟨view8, 7⟩,
  ⟨view9, 65536⟩,
  ⟨view10, 65536⟩,
  ⟨view11, 65536⟩,
  ⟨view12, 65536⟩,
  ⟨view13, 128⟩,
  ⟨view14, 65536⟩,
  ⟨view15, 65536⟩,
  ⟨view16, 65536⟩]

end Airbender.Compiler.UnifiedRegionLengths.Column3
