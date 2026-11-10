import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

noncomputable def source0 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part0_0 from (UnifiedReduced.Setup.nativeZeroData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination0_0 : Setup.Block := part0_0.get ⟨0, by decide +kernel⟩

column_blocks_part part0_1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination0_1 : Setup.Block := part0_1.get ⟨0, by decide +kernel⟩

noncomputable def target0 : List Setup.Block := part0_0 ++ part0_1

noncomputable def source1 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part1_0 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination1_0 : Setup.Block := part1_0.get ⟨0, by decide +kernel⟩

column_blocks_part part1_1 from (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination1_1 : Setup.Block := part1_1.get ⟨0, by decide +kernel⟩

noncomputable def target1 : List Setup.Block := part1_0 ++ part1_1

noncomputable def source2 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part2_0 from (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination2_0 : Setup.Block := part2_0.get ⟨0, by decide +kernel⟩

column_blocks_part part2_1 from (UnifiedReduced.Setup.nativeCleanupData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination2_1 : Setup.Block := part2_1.get ⟨0, by decide +kernel⟩

column_blocks_part part2_2 from (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination2_2 : Setup.Block := part2_2.get ⟨0, by decide +kernel⟩

noncomputable def target2 : List Setup.Block := part2_0 ++ part2_1 ++ part2_2

noncomputable def source3 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part3_0 from (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination3_0 : Setup.Block := part3_0.get ⟨0, by decide +kernel⟩

noncomputable def target3 : List Setup.Block := part3_0

noncomputable def source4 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part4_0 from (UnifiedReduced.Setup.nativeByteSignData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination4_0 : Setup.Block := part4_0.get ⟨0, by decide +kernel⟩

noncomputable def target4 : List Setup.Block := part4_0

noncomputable def source5 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part5_0 from (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination5_0 : Setup.Block := part5_0.get ⟨0, by decide +kernel⟩

noncomputable def target5 : List Setup.Block := part5_0

noncomputable def source6 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part6_0 from (UnifiedReduced.Setup.nativeSignData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination6_0 : Setup.Block := part6_0.get ⟨0, by decide +kernel⟩

noncomputable def target6 : List Setup.Block := part6_0

noncomputable def source7 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part7_0 from (UnifiedReduced.Setup.nativeTruncationData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination7_0 : Setup.Block := part7_0.get ⟨0, by decide +kernel⟩

noncomputable def target7 : List Setup.Block := part7_0

noncomputable def source8 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part8_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination8_0 : Setup.Block := part8_0.get ⟨0, by decide +kernel⟩

noncomputable def target8 : List Setup.Block := part8_0

noncomputable def source9 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part9_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination9_0 : Setup.Block := part9_0.get ⟨0, by decide +kernel⟩

noncomputable def target9 : List Setup.Block := part9_0

noncomputable def source10 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part10_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination10_0 : Setup.Block := part10_0.get ⟨0, by decide +kernel⟩

noncomputable def target10 : List Setup.Block := part10_0

noncomputable def source11 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part11_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 3 stop 4
noncomputable def destination11_0 : Setup.Block := part11_0.get ⟨0, by decide +kernel⟩

noncomputable def target11 : List Setup.Block := part11_0

noncomputable def source15 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part15_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination15_0 : Setup.Block := part15_0.get ⟨0, by decide +kernel⟩

noncomputable def target15 : List Setup.Block := part15_0

noncomputable def source16 : Setup.Block := original.get ⟨16, by decide +kernel⟩

column_blocks_part part16_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination16_0 : Setup.Block := part16_0.get ⟨0, by decide +kernel⟩

noncomputable def target16 : List Setup.Block := part16_0

noncomputable def source17 : Setup.Block := original.get ⟨17, by decide +kernel⟩

column_blocks_part part17_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 3 stop 4
noncomputable def destination17_0 : Setup.Block := part17_0.get ⟨0, by decide +kernel⟩

noncomputable def target17 : List Setup.Block := part17_0

noncomputable def source18 : Setup.Block := original.get ⟨18, by decide +kernel⟩

column_blocks_part part18_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 4 stop 5
noncomputable def destination18_0 : Setup.Block := part18_0.get ⟨0, by decide +kernel⟩

noncomputable def target18 : List Setup.Block := part18_0

noncomputable def source19 : Setup.Block := original.get ⟨19, by decide +kernel⟩

column_blocks_part part19_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 5 stop 6
noncomputable def destination19_0 : Setup.Block := part19_0.get ⟨0, by decide +kernel⟩

noncomputable def target19 : List Setup.Block := part19_0

noncomputable def source20 : Setup.Block := original.get ⟨20, by decide +kernel⟩

column_blocks_part part20_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 6 stop 7
noncomputable def destination20_0 : Setup.Block := part20_0.get ⟨0, by decide +kernel⟩

noncomputable def target20 : List Setup.Block := part20_0

noncomputable def source21 : Setup.Block := original.get ⟨21, by decide +kernel⟩

column_blocks_part part21_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 7 stop 8
noncomputable def destination21_0 : Setup.Block := part21_0.get ⟨0, by decide +kernel⟩

noncomputable def target21 : List Setup.Block := part21_0

noncomputable def source22 : Setup.Block := original.get ⟨22, by decide +kernel⟩

column_blocks_part part22_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 8 stop 9
noncomputable def destination22_0 : Setup.Block := part22_0.get ⟨0, by decide +kernel⟩

noncomputable def target22 : List Setup.Block := part22_0

noncomputable def source23 : Setup.Block := original.get ⟨23, by decide +kernel⟩

column_blocks_part part23_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 9 stop 10
noncomputable def destination23_0 : Setup.Block := part23_0.get ⟨0, by decide +kernel⟩

noncomputable def target23 : List Setup.Block := part23_0

noncomputable def source24 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 10 stop 11
noncomputable def destination24_0 : Setup.Block := part24_0.get ⟨0, by decide +kernel⟩

noncomputable def target24 : List Setup.Block := part24_0

noncomputable def source25 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part25_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 11 stop 12
noncomputable def destination25_0 : Setup.Block := part25_0.get ⟨0, by decide +kernel⟩

noncomputable def target25 : List Setup.Block := part25_0

noncomputable def source26 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part26_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 12 stop 13
noncomputable def destination26_0 : Setup.Block := part26_0.get ⟨0, by decide +kernel⟩

noncomputable def target26 : List Setup.Block := part26_0

noncomputable def source27 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part27_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 13 stop 14
noncomputable def destination27_0 : Setup.Block := part27_0.get ⟨0, by decide +kernel⟩

noncomputable def target27 : List Setup.Block := part27_0

noncomputable def source28 : Setup.Block := original.get ⟨28, by decide +kernel⟩

column_blocks_part part28_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 14 stop 15
noncomputable def destination28_0 : Setup.Block := part28_0.get ⟨0, by decide +kernel⟩

noncomputable def target28 : List Setup.Block := part28_0

noncomputable def source29 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part29_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 15 stop 16
noncomputable def destination29_0 : Setup.Block := part29_0.get ⟨0, by decide +kernel⟩

noncomputable def target29 : List Setup.Block := part29_0

noncomputable def source30 : Setup.Block := original.get ⟨30, by decide +kernel⟩

column_blocks_part part30_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 16 stop 17
noncomputable def destination30_0 : Setup.Block := part30_0.get ⟨0, by decide +kernel⟩

noncomputable def target30 : List Setup.Block := part30_0

noncomputable def source31 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part31_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 17 stop 18
noncomputable def destination31_0 : Setup.Block := part31_0.get ⟨0, by decide +kernel⟩

noncomputable def target31 : List Setup.Block := part31_0

noncomputable def source32 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part32_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 18 stop 19
noncomputable def destination32_0 : Setup.Block := part32_0.get ⟨0, by decide +kernel⟩

column_blocks_part part32_1 from (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination32_1 : Setup.Block := part32_1.get ⟨0, by decide +kernel⟩

noncomputable def target32 : List Setup.Block := part32_0 ++ part32_1

end Airbender.Compiler.UnifiedPrefixNative.Column1
