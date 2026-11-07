import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column1.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.UnifiedRegionLengths.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem binding0 : Airbender.Compiler.UnifiedPrefixNative.Column1.part0_0 = view0.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets0_binding

theorem binding1 : Airbender.Compiler.UnifiedPrefixNative.Column1.part0_1 = view1.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 1).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets0_binding

theorem binding2 : Airbender.Compiler.UnifiedPrefixNative.Column1.part1_0 = view2.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets1_binding

theorem binding3 : Airbender.Compiler.UnifiedPrefixNative.Column1.part1_1 = view3.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 1).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets1_binding

theorem binding4 : Airbender.Compiler.UnifiedPrefixNative.Column1.part2_0 = view4.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets2_binding

theorem binding5 : Airbender.Compiler.UnifiedPrefixNative.Column1.part2_1 = view5.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 1).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets2_binding

theorem binding6 : Airbender.Compiler.UnifiedPrefixNative.Column1.part2_2 = view6.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 2).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets2_binding

theorem binding7 : Airbender.Compiler.UnifiedPrefixNative.Column1.part3_0 = view7.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets3_binding

theorem binding8 : Airbender.Compiler.UnifiedPrefixNative.Column1.part4_0 = view8.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets4_binding

theorem binding9 : Airbender.Compiler.UnifiedPrefixNative.Column1.part5_0 = view9.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets5_binding

theorem binding10 : Airbender.Compiler.UnifiedPrefixNative.Column1.part6_0 = view10.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets6_binding

theorem binding11 : Airbender.Compiler.UnifiedPrefixNative.Column1.part7_0 = view11.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets7_binding

theorem binding12 : Airbender.Compiler.UnifiedPrefixNative.Column1.part8_0 = view12.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets8_binding

theorem binding13 : Airbender.Compiler.UnifiedPrefixNative.Column1.part9_0 = view13.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets9_binding

theorem binding14 : Airbender.Compiler.UnifiedPrefixNative.Column1.part10_0 = view14.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets10_binding

theorem binding15 : Airbender.Compiler.UnifiedPrefixNative.Column1.part11_0 = view15.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets11_binding

numeric_data_binding binding16 : Airbender.Compiler.UnifiedPrefixNative.Column1.part13_1 = view16.map BlockCode.decode

theorem binding17 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_0 = view17.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding18 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_1 = view18.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 1).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding19 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_2 = view19.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 2).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding20 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_3 = view20.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 3).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding21 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_4 = view21.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 4).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding22 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_5 = view22.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 5).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding23 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_6 = view23.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 6).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding24 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_7 = view24.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 7).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding25 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_8 = view25.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 8).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding26 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_9 = view26.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 9).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding27 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_10 = view27.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 10).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding28 : Airbender.Compiler.UnifiedPrefixNative.Column1.part14_11 = view28.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 11).take 1) Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.targets_binding

theorem binding29 : Airbender.Compiler.UnifiedPrefixNative.Column1.part15_0 = view29.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets15_binding

theorem binding30 : Airbender.Compiler.UnifiedPrefixNative.Column1.part16_0 = view30.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets16_binding

theorem binding31 : Airbender.Compiler.UnifiedPrefixNative.Column1.part17_0 = view31.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets17_binding

theorem binding32 : Airbender.Compiler.UnifiedPrefixNative.Column1.part18_0 = view32.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets18_binding

theorem binding33 : Airbender.Compiler.UnifiedPrefixNative.Column1.part19_0 = view33.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets19_binding

theorem binding34 : Airbender.Compiler.UnifiedPrefixNative.Column1.part20_0 = view34.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets20_binding

theorem binding35 : Airbender.Compiler.UnifiedPrefixNative.Column1.part21_0 = view35.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets21_binding

theorem binding36 : Airbender.Compiler.UnifiedPrefixNative.Column1.part22_0 = view36.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets22_binding

theorem binding37 : Airbender.Compiler.UnifiedPrefixNative.Column1.part23_0 = view37.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets23_binding

theorem binding38 : Airbender.Compiler.UnifiedPrefixNative.Column1.part24_0 = view38.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets24_binding

theorem binding39 : Airbender.Compiler.UnifiedPrefixNative.Column1.part25_0 = view39.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets25_binding

theorem binding40 : Airbender.Compiler.UnifiedPrefixNative.Column1.part26_0 = view40.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets26_binding

theorem binding41 : Airbender.Compiler.UnifiedPrefixNative.Column1.part27_0 = view41.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets27_binding

theorem binding42 : Airbender.Compiler.UnifiedPrefixNative.Column1.part28_0 = view42.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets28_binding

theorem binding43 : Airbender.Compiler.UnifiedPrefixNative.Column1.part29_0 = view43.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets29_binding

theorem binding44 : Airbender.Compiler.UnifiedPrefixNative.Column1.part30_0 = view44.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets30_binding

theorem binding45 : Airbender.Compiler.UnifiedPrefixNative.Column1.part31_0 = view45.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets31_binding

theorem binding46 : Airbender.Compiler.UnifiedPrefixNative.Column1.part32_0 = view46.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets32_binding

theorem binding47 : Airbender.Compiler.UnifiedPrefixNative.Column1.part32_1 = view47.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 1).take 1) Airbender.Compiler.UnifiedFixedSpans.Column1.targets32_binding

numeric_data_binding binding48 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_0 = view48.map BlockCode.decode

numeric_data_binding binding49 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_1 = view49.map BlockCode.decode

numeric_data_binding binding50 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_2 = view50.map BlockCode.decode

numeric_data_binding binding51 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_3 = view51.map BlockCode.decode

numeric_data_binding binding52 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_4 = view52.map BlockCode.decode

numeric_data_binding binding53 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_5 = view53.map BlockCode.decode

numeric_data_binding binding54 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_6 = view54.map BlockCode.decode

numeric_data_binding binding55 : Airbender.Compiler.UnifiedPrefixNative.Column1.part33_7 = view55.map BlockCode.decode

end Airbender.Compiler.UnifiedRegionLengths.Column1
