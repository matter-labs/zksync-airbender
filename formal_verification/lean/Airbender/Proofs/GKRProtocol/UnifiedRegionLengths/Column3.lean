import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column3.Certificate

namespace Airbender.Compiler.UnifiedRegionLengths.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem length0 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_0.map Setup.Block.length).sum = 1 := by
  rw [binding0]
  exact facts ⟨0, by decide +kernel⟩

theorem length1 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_1.map Setup.Block.length).sum = 131072 := by
  rw [binding1]
  exact facts ⟨1, by decide +kernel⟩

theorem length2 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_2.map Setup.Block.length).sum = 65536 := by
  rw [binding2]
  exact facts ⟨2, by decide +kernel⟩

theorem length3 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_3.map Setup.Block.length).sum = 256 := by
  rw [binding3]
  exact facts ⟨3, by decide +kernel⟩

theorem length4 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_4.map Setup.Block.length).sum = 65536 := by
  rw [binding4]
  exact facts ⟨4, by decide +kernel⟩

theorem length5 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_5.map Setup.Block.length).sum = 65536 := by
  rw [binding5]
  exact facts ⟨5, by decide +kernel⟩

theorem length6 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part0_6.map Setup.Block.length).sum = 1 := by
  rw [binding6]
  exact facts ⟨6, by decide +kernel⟩

theorem length7 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part1_0.map Setup.Block.length).sum = 262136 := by
  rw [binding7]
  exact facts ⟨7, by decide +kernel⟩

theorem length8 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part1_1.map Setup.Block.length).sum = 7 := by
  rw [binding8]
  exact facts ⟨8, by decide +kernel⟩

theorem length9 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_1.map Setup.Block.length).sum = 65536 := by
  rw [binding9]
  exact facts ⟨9, by decide +kernel⟩

theorem length10 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_2.map Setup.Block.length).sum = 65536 := by
  rw [binding10]
  exact facts ⟨10, by decide +kernel⟩

theorem length11 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_3.map Setup.Block.length).sum = 65536 := by
  rw [binding11]
  exact facts ⟨11, by decide +kernel⟩

theorem length12 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_4.map Setup.Block.length).sum = 65536 := by
  rw [binding12]
  exact facts ⟨12, by decide +kernel⟩

theorem length13 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_5.map Setup.Block.length).sum = 128 := by
  rw [binding13]
  exact facts ⟨13, by decide +kernel⟩

theorem length14 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_6.map Setup.Block.length).sum = 65536 := by
  rw [binding14]
  exact facts ⟨14, by decide +kernel⟩

theorem length15 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_7.map Setup.Block.length).sum = 65536 := by
  rw [binding15]
  exact facts ⟨15, by decide +kernel⟩

theorem length16 : (Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.part2_8.map Setup.Block.length).sum = 65536 := by
  rw [binding16]
  exact facts ⟨16, by decide +kernel⟩

end Airbender.Compiler.UnifiedRegionLengths.Column3
