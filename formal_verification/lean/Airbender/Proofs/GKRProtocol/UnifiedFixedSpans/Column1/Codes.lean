import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column1.Data
import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupSpans

namespace Airbender.Compiler.UnifiedFixedSpans.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

set_option maxHeartbeats 2000000

import_setup_code_capture from "artifacts/setup/unified.json" [
  source0 := column 1 block_start 0 block_count 1 unpacked,
  target0_0 := region 0 column 1 block_start 0 block_count 1 packed_bytes 0,
  target0_1 := region 1 column 1 block_start 0 block_count 1 packed_bytes 0,
  source1 := column 1 block_start 1 block_count 1 unpacked,
  target1_0 := region 1 column 1 block_start 1 block_count 1 packed_bytes 0,
  target1_1 := region 2 column 1 block_start 0 block_count 1 packed_bytes 0,
  source2 := column 1 block_start 2 block_count 1 unpacked,
  target2_0 := region 2 column 1 block_start 1 block_count 1 packed_bytes 0,
  target2_1 := region 2 column 1 block_start 2 block_count 1 packed_bytes 0,
  target2_2 := region 3 column 1 block_start 0 block_count 1 packed_bytes 0,
  source3 := column 1 block_start 3 block_count 1 unpacked,
  target3_0 := region 3 column 1 block_start 1 block_count 1 packed_bytes 0,
  source4 := column 1 block_start 4 block_count 1 unpacked,
  target4_0 := region 3 column 1 block_start 2 block_count 1 packed_bytes 0,
  source5 := column 1 block_start 5 block_count 1 unpacked,
  target5_0 := region 5 column 1 block_start 0 block_count 1 packed_bytes 0,
  source6 := column 1 block_start 6 block_count 1 unpacked,
  target6_0 := region 5 column 1 block_start 1 block_count 1 packed_bytes 0,
  source7 := column 1 block_start 7 block_count 1 unpacked,
  target7_0 := region 8 column 1 block_start 0 block_count 1 packed_bytes 0,
  source8 := column 1 block_start 8 block_count 1 unpacked,
  target8_0 := region 9 column 1 block_start 0 block_count 1 packed_bytes 0,
  source9 := column 1 block_start 9 block_count 1 unpacked,
  target9_0 := region 9 column 1 block_start 1 block_count 1 packed_bytes 0,
  source10 := column 1 block_start 10 block_count 1 unpacked,
  target10_0 := region 9 column 1 block_start 2 block_count 1 packed_bytes 0,
  source11 := column 1 block_start 11 block_count 1 unpacked,
  target11_0 := region 9 column 1 block_start 3 block_count 1 packed_bytes 0,
  source15 := column 1 block_start 15 block_count 1 unpacked,
  target15_0 := region 51 column 1 block_start 1 block_count 1 packed_bytes 0,
  source16 := column 1 block_start 16 block_count 1 unpacked,
  target16_0 := region 51 column 1 block_start 2 block_count 1 packed_bytes 0,
  source17 := column 1 block_start 17 block_count 1 unpacked,
  target17_0 := region 51 column 1 block_start 3 block_count 1 packed_bytes 0,
  source18 := column 1 block_start 18 block_count 1 unpacked,
  target18_0 := region 51 column 1 block_start 4 block_count 1 packed_bytes 0,
  source19 := column 1 block_start 19 block_count 1 unpacked,
  target19_0 := region 51 column 1 block_start 5 block_count 1 packed_bytes 0,
  source20 := column 1 block_start 20 block_count 1 unpacked,
  target20_0 := region 51 column 1 block_start 6 block_count 1 packed_bytes 0,
  source21 := column 1 block_start 21 block_count 1 unpacked,
  target21_0 := region 51 column 1 block_start 7 block_count 1 packed_bytes 0,
  source22 := column 1 block_start 22 block_count 1 unpacked,
  target22_0 := region 51 column 1 block_start 8 block_count 1 packed_bytes 0,
  source23 := column 1 block_start 23 block_count 1 unpacked,
  target23_0 := region 51 column 1 block_start 9 block_count 1 packed_bytes 0,
  source24 := column 1 block_start 24 block_count 1 unpacked,
  target24_0 := region 51 column 1 block_start 10 block_count 1 packed_bytes 0,
  source25 := column 1 block_start 25 block_count 1 unpacked,
  target25_0 := region 51 column 1 block_start 11 block_count 1 packed_bytes 0,
  source26 := column 1 block_start 26 block_count 1 unpacked,
  target26_0 := region 51 column 1 block_start 12 block_count 1 packed_bytes 0,
  source27 := column 1 block_start 27 block_count 1 unpacked,
  target27_0 := region 51 column 1 block_start 13 block_count 1 packed_bytes 0,
  source28 := column 1 block_start 28 block_count 1 unpacked,
  target28_0 := region 51 column 1 block_start 14 block_count 1 packed_bytes 0,
  source29 := column 1 block_start 29 block_count 1 unpacked,
  target29_0 := region 51 column 1 block_start 15 block_count 1 packed_bytes 0,
  source30 := column 1 block_start 30 block_count 1 unpacked,
  target30_0 := region 51 column 1 block_start 16 block_count 1 packed_bytes 0,
  source31 := column 1 block_start 31 block_count 1 unpacked,
  target31_0 := region 51 column 1 block_start 17 block_count 1 packed_bytes 0,
  source32 := column 1 block_start 32 block_count 1 unpacked,
  target32_0 := region 51 column 1 block_start 18 block_count 1 packed_bytes 0,
  target32_1 := region 52 column 1 block_start 0 block_count 1 packed_bytes 0]

def targets0 : List BlockCode := target0_0 ++ target0_1
def targets1 : List BlockCode := target1_0 ++ target1_1
def targets2 : List BlockCode := target2_0 ++ target2_1 ++ target2_2
def targets3 : List BlockCode := target3_0
def targets4 : List BlockCode := target4_0
def targets5 : List BlockCode := target5_0
def targets6 : List BlockCode := target6_0
def targets7 : List BlockCode := target7_0
def targets8 : List BlockCode := target8_0
def targets9 : List BlockCode := target9_0
def targets10 : List BlockCode := target10_0
def targets11 : List BlockCode := target11_0
def targets15 : List BlockCode := target15_0
def targets16 : List BlockCode := target16_0
def targets17 : List BlockCode := target17_0
def targets18 : List BlockCode := target18_0
def targets19 : List BlockCode := target19_0
def targets20 : List BlockCode := target20_0
def targets21 : List BlockCode := target21_0
def targets22 : List BlockCode := target22_0
def targets23 : List BlockCode := target23_0
def targets24 : List BlockCode := target24_0
def targets25 : List BlockCode := target25_0
def targets26 : List BlockCode := target26_0
def targets27 : List BlockCode := target27_0
def targets28 : List BlockCode := target28_0
def targets29 : List BlockCode := target29_0
def targets30 : List BlockCode := target30_0
def targets31 : List BlockCode := target31_0
def targets32 : List BlockCode := target32_0 ++ target32_1

def requests : List PackedSetupSpans.Request := [
  ⟨source0.get ⟨0, by decide +kernel⟩, targets0⟩,
  ⟨source1.get ⟨0, by decide +kernel⟩, targets1⟩,
  ⟨source2.get ⟨0, by decide +kernel⟩, targets2⟩,
  ⟨source3.get ⟨0, by decide +kernel⟩, targets3⟩,
  ⟨source4.get ⟨0, by decide +kernel⟩, targets4⟩,
  ⟨source5.get ⟨0, by decide +kernel⟩, targets5⟩,
  ⟨source6.get ⟨0, by decide +kernel⟩, targets6⟩,
  ⟨source7.get ⟨0, by decide +kernel⟩, targets7⟩,
  ⟨source8.get ⟨0, by decide +kernel⟩, targets8⟩,
  ⟨source9.get ⟨0, by decide +kernel⟩, targets9⟩,
  ⟨source10.get ⟨0, by decide +kernel⟩, targets10⟩,
  ⟨source11.get ⟨0, by decide +kernel⟩, targets11⟩,
  ⟨source15.get ⟨0, by decide +kernel⟩, targets15⟩,
  ⟨source16.get ⟨0, by decide +kernel⟩, targets16⟩,
  ⟨source17.get ⟨0, by decide +kernel⟩, targets17⟩,
  ⟨source18.get ⟨0, by decide +kernel⟩, targets18⟩,
  ⟨source19.get ⟨0, by decide +kernel⟩, targets19⟩,
  ⟨source20.get ⟨0, by decide +kernel⟩, targets20⟩,
  ⟨source21.get ⟨0, by decide +kernel⟩, targets21⟩,
  ⟨source22.get ⟨0, by decide +kernel⟩, targets22⟩,
  ⟨source23.get ⟨0, by decide +kernel⟩, targets23⟩,
  ⟨source24.get ⟨0, by decide +kernel⟩, targets24⟩,
  ⟨source25.get ⟨0, by decide +kernel⟩, targets25⟩,
  ⟨source26.get ⟨0, by decide +kernel⟩, targets26⟩,
  ⟨source27.get ⟨0, by decide +kernel⟩, targets27⟩,
  ⟨source28.get ⟨0, by decide +kernel⟩, targets28⟩,
  ⟨source29.get ⟨0, by decide +kernel⟩, targets29⟩,
  ⟨source30.get ⟨0, by decide +kernel⟩, targets30⟩,
  ⟨source31.get ⟨0, by decide +kernel⟩, targets31⟩,
  ⟨source32.get ⟨0, by decide +kernel⟩, targets32⟩]

end Airbender.Compiler.UnifiedFixedSpans.Column1
