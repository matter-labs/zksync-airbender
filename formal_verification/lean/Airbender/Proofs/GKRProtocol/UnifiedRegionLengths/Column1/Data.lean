import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column1.Bindings
import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Bindings
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit12
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit13
import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit33
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupLengths

namespace Airbender.Compiler.UnifiedRegionLengths.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

-- Import only fixed target pieces that have no existing numeric view.
import_setup_code_capture from "artifacts/setup/unified.json" [
  extra16 := region 47 column 1 block_start 0 block_count 1 packed_bytes 0,
  extra48 := region 52 column 1 block_start 1 block_count 1 packed_bytes 0,
  extra49 := region 52 column 1 block_start 2 block_count 1 packed_bytes 0,
  extra50 := region 53 column 1 block_start 0 block_count 1 packed_bytes 0,
  extra51 := region 53 column 1 block_start 1 block_count 1 packed_bytes 0,
  extra52 := region 53 column 1 block_start 2 block_count 1 packed_bytes 0,
  extra53 := region 54 column 1 block_start 0 block_count 1 packed_bytes 0,
  extra54 := region 54 column 1 block_start 1 block_count 1 packed_bytes 0,
  extra55 := region 54 column 1 block_start 2 block_count 1 packed_bytes 0]

noncomputable def view0 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target0_0
noncomputable def view1 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target0_1
noncomputable def view2 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target1_0
noncomputable def view3 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target1_1
noncomputable def view4 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target2_0
noncomputable def view5 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target2_1
noncomputable def view6 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target2_2
noncomputable def view7 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target3_0
noncomputable def view8 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target4_0
noncomputable def view9 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target5_0
noncomputable def view10 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target6_0
noncomputable def view11 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target7_0
noncomputable def view12 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target8_0
noncomputable def view13 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target9_0
noncomputable def view14 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target10_0
noncomputable def view15 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target11_0
noncomputable def view16 : List BlockCode := extra16
noncomputable def view17 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target0
noncomputable def view18 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target1
noncomputable def view19 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target2
noncomputable def view20 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target3
noncomputable def view21 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target4
noncomputable def view22 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target5
noncomputable def view23 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target6
noncomputable def view24 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target7
noncomputable def view25 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target8
noncomputable def view26 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target9
noncomputable def view27 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target10
noncomputable def view28 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.target11
noncomputable def view29 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target15_0
noncomputable def view30 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target16_0
noncomputable def view31 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target17_0
noncomputable def view32 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target18_0
noncomputable def view33 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target19_0
noncomputable def view34 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target20_0
noncomputable def view35 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target21_0
noncomputable def view36 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target22_0
noncomputable def view37 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target23_0
noncomputable def view38 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target24_0
noncomputable def view39 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target25_0
noncomputable def view40 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target26_0
noncomputable def view41 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target27_0
noncomputable def view42 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target28_0
noncomputable def view43 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target29_0
noncomputable def view44 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target30_0
noncomputable def view45 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target31_0
noncomputable def view46 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target32_0
noncomputable def view47 : List BlockCode := Airbender.Compiler.UnifiedFixedSpans.Column1.target32_1
noncomputable def view48 : List BlockCode := extra48
noncomputable def view49 : List BlockCode := extra49
noncomputable def view50 : List BlockCode := extra50
noncomputable def view51 : List BlockCode := extra51
noncomputable def view52 : List BlockCode := extra52
noncomputable def view53 : List BlockCode := extra53
noncomputable def view54 : List BlockCode := extra54
noncomputable def view55 : List BlockCode := extra55

-- These views support kernel proofs. They do not need runtime compilation.
noncomputable def requests : List Request := [
  ⟨view0, 1⟩,
  ⟨view1, 1⟩,
  ⟨view2, 131071⟩,
  ⟨view3, 2⟩,
  ⟨view4, 65532⟩,
  ⟨view5, 2⟩,
  ⟨view6, 2⟩,
  ⟨view7, 126⟩,
  ⟨view8, 128⟩,
  ⟨view9, 32768⟩,
  ⟨view10, 32768⟩,
  ⟨view11, 65536⟩,
  ⟨view12, 65536⟩,
  ⟨view13, 65536⟩,
  ⟨view14, 65536⟩,
  ⟨view15, 65536⟩,
  ⟨view16, 1⟩,
  ⟨view17, 65280⟩,
  ⟨view18, 255⟩,
  ⟨view19, 1⟩,
  ⟨view20, 65280⟩,
  ⟨view21, 255⟩,
  ⟨view22, 1⟩,
  ⟨view23, 65280⟩,
  ⟨view24, 255⟩,
  ⟨view25, 1⟩,
  ⟨view26, 65280⟩,
  ⟨view27, 255⟩,
  ⟨view28, 1⟩,
  ⟨view29, 7⟩,
  ⟨view30, 16⟩,
  ⟨view31, 10⟩,
  ⟨view32, 14⟩,
  ⟨view33, 4⟩,
  ⟨view34, 4⟩,
  ⟨view35, 4⟩,
  ⟨view36, 4⟩,
  ⟨view37, 14⟩,
  ⟨view38, 4⟩,
  ⟨view39, 12⟩,
  ⟨view40, 6⟩,
  ⟨view41, 4⟩,
  ⟨view42, 4⟩,
  ⟨view43, 8⟩,
  ⟨view44, 4⟩,
  ⟨view45, 4⟩,
  ⟨view46, 4⟩,
  ⟨view47, 1⟩,
  ⟨view48, 65280⟩,
  ⟨view49, 255⟩,
  ⟨view50, 1⟩,
  ⟨view51, 65280⟩,
  ⟨view52, 255⟩,
  ⟨view53, 1⟩,
  ⟨view54, 65280⟩,
  ⟨view55, 255⟩]

end Airbender.Compiler.UnifiedRegionLengths.Column1
