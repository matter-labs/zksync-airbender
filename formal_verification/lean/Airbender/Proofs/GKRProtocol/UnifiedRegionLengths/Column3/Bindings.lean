import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column3.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.UnifiedRegionLengths.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem binding0 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_0 = view0.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 0).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

theorem binding1 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_1 = view1.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 1).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

theorem binding2 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_2 = view2.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 2).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

theorem binding3 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_3 = view3.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 3).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

theorem binding4 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_4 = view4.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 4).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

theorem binding5 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_5 = view5.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 5).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

theorem binding6 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_6 = view6.map BlockCode.decode :=
  congrArg (fun blocks : List Setup.Block => (blocks.drop 6).take 1) Airbender.Compiler.UnifiedFixedSpans.Column3.targets0_binding

numeric_data_binding binding7 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part1_0 = view7.map BlockCode.decode

numeric_data_binding binding8 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part1_1 = view8.map BlockCode.decode

numeric_data_binding binding9 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_1 = view9.map BlockCode.decode

numeric_data_binding binding10 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_2 = view10.map BlockCode.decode

numeric_data_binding binding11 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_3 = view11.map BlockCode.decode

numeric_data_binding binding12 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_4 = view12.map BlockCode.decode

numeric_data_binding binding13 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_5 = view13.map BlockCode.decode

numeric_data_binding binding14 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_6 = view14.map BlockCode.decode

numeric_data_binding binding15 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_7 = view15.map BlockCode.decode

numeric_data_binding binding16 : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_8 = view16.map BlockCode.decode

end Airbender.Compiler.UnifiedRegionLengths.Column3
