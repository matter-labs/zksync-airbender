import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column1.Certificate

namespace Airbender.Compiler.ShiftPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.source0_binding, Airbender.Compiler.ShiftPrefixChecks.Column1.target0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨0, by decide +kernel⟩).1

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 524545 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.source0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨0, by decide +kernel⟩).2

theorem checkedRegion0Part0Length : (target0Region0.map Setup.Block.length).sum = 1 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨1, by decide +kernel⟩).2

theorem checkedRegion1Part0Length : (target0Region1.map Setup.Block.length).sum = 256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨2, by decide +kernel⟩).2

theorem checkedRegion2Part0Length : (target0Region2.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨3, by decide +kernel⟩).2

theorem checkedRegion3Part0Length : (target0Region3.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨4, by decide +kernel⟩).2

theorem checkedRegion4Part0Length : (target0Region4.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨5, by decide +kernel⟩).2

theorem checkedRegion5Part0Length : (target0Region5.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨6, by decide +kernel⟩).2

theorem checkedRegion6Part0Length : (target0Region6.map Setup.Block.length).sum = 262144 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column1.target0Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column1.facts ⟨7, by decide +kernel⟩).2

end Airbender.Compiler.ShiftPrefixNative.Column1
