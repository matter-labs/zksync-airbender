import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column2.Certificate

namespace Airbender.Compiler.ShiftPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source0_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨0, by decide +kernel⟩).1

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 20673 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨0, by decide +kernel⟩).2

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source1_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨1, by decide +kernel⟩).1

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 1340 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨1, by decide +kernel⟩).2

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source2_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨2, by decide +kernel⟩).1

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 2756 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨2, by decide +kernel⟩).2

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source3_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨3, by decide +kernel⟩).1

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 16192 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨3, by decide +kernel⟩).2

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source4_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨4, by decide +kernel⟩).1

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 2800 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨4, by decide +kernel⟩).2

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source5_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨5, by decide +kernel⟩).1

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1504 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨5, by decide +kernel⟩).2

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source6_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨6, by decide +kernel⟩).1

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 19760 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨6, by decide +kernel⟩).2

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source7_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target7_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨7, by decide +kernel⟩).1

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 21056 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source7_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨7, by decide +kernel⟩).2

theorem chunkChecked8 : normalizeSetupBlocks original8 = normalizeSetupBlocks target8 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source8_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target8_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨8, by decide +kernel⟩).1

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 1460 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source8_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨8, by decide +kernel⟩).2

theorem chunkChecked9 : normalizeSetupBlocks original9 = normalizeSetupBlocks target9 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source9_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target9_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨9, by decide +kernel⟩).1

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 2700 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source9_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨9, by decide +kernel⟩).2

theorem chunkChecked10 : normalizeSetupBlocks original10 = normalizeSetupBlocks target10 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source10_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target10_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨10, by decide +kernel⟩).1

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 16000 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source10_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨10, by decide +kernel⟩).2

theorem chunkChecked11 : normalizeSetupBlocks original11 = normalizeSetupBlocks target11 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source11_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target11_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨11, by decide +kernel⟩).1

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 3040 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source11_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨11, by decide +kernel⟩).2

theorem chunkChecked12 : normalizeSetupBlocks original12 = normalizeSetupBlocks target12 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source12_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target12_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨12, by decide +kernel⟩).1

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 1488 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source12_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨12, by decide +kernel⟩).2

theorem chunkChecked13 : normalizeSetupBlocks original13 = normalizeSetupBlocks target13 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source13_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target13_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨13, by decide +kernel⟩).1

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 19280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source13_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨13, by decide +kernel⟩).2

theorem chunkChecked14 : normalizeSetupBlocks original14 = normalizeSetupBlocks target14 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source14_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target14_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨14, by decide +kernel⟩).1

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 21440 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source14_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨14, by decide +kernel⟩).2

theorem chunkChecked15 : normalizeSetupBlocks original15 = normalizeSetupBlocks target15 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source15_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target15_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨15, by decide +kernel⟩).1

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 1580 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source15_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨15, by decide +kernel⟩).2

theorem chunkChecked16 : normalizeSetupBlocks original16 = normalizeSetupBlocks target16 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source16_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target16_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨16, by decide +kernel⟩).1

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 2644 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source16_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨16, by decide +kernel⟩).2

theorem chunkChecked17 : normalizeSetupBlocks original17 = normalizeSetupBlocks target17 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source17_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target17_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨17, by decide +kernel⟩).1

theorem chunkLength17 : (original17.map Setup.Block.length).sum = 15808 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source17_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨17, by decide +kernel⟩).2

theorem chunkChecked18 : normalizeSetupBlocks original18 = normalizeSetupBlocks target18 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source18_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target18_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨18, by decide +kernel⟩).1

theorem chunkLength18 : (original18.map Setup.Block.length).sum = 3280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source18_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨18, by decide +kernel⟩).2

theorem chunkChecked19 : normalizeSetupBlocks original19 = normalizeSetupBlocks target19 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source19_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target19_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨19, by decide +kernel⟩).1

theorem chunkLength19 : (original19.map Setup.Block.length).sum = 1472 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source19_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨19, by decide +kernel⟩).2

theorem chunkChecked20 : normalizeSetupBlocks original20 = normalizeSetupBlocks target20 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source20_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target20_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨20, by decide +kernel⟩).1

theorem chunkLength20 : (original20.map Setup.Block.length).sum = 18800 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source20_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨20, by decide +kernel⟩).2

theorem chunkChecked21 : normalizeSetupBlocks original21 = normalizeSetupBlocks target21 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source21_binding, Airbender.Compiler.ShiftPrefixChecks.Column2.target21_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨21, by decide +kernel⟩).1

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 329472 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.source21_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨21, by decide +kernel⟩).2

theorem checkedRegion0Part0Length : (target0Region0.map Setup.Block.length).sum = 1 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target0Region0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨22, by decide +kernel⟩).2

theorem checkedRegion1Part0Length : (target0Region1.map Setup.Block.length).sum = 256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target0Region1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨23, by decide +kernel⟩).2

theorem checkedRegion2Part0Length : (target0Region2.map Setup.Block.length).sum = 20416 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target0Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨24, by decide +kernel⟩).2

theorem checkedRegion2Part1Length : (target1Region2.map Setup.Block.length).sum = 1340 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target1Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨25, by decide +kernel⟩).2

theorem checkedRegion2Part2Length : (target2Region2.map Setup.Block.length).sum = 2756 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target2Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨26, by decide +kernel⟩).2

theorem checkedRegion2Part3Length : (target3Region2.map Setup.Block.length).sum = 16192 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target3Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨27, by decide +kernel⟩).2

theorem checkedRegion2Part4Length : (target4Region2.map Setup.Block.length).sum = 2800 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target4Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨28, by decide +kernel⟩).2

theorem checkedRegion2Part5Length : (target5Region2.map Setup.Block.length).sum = 1504 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target5Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨29, by decide +kernel⟩).2

theorem checkedRegion2Part6Length : (target6Region2.map Setup.Block.length).sum = 19760 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target6Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨30, by decide +kernel⟩).2

theorem checkedRegion2Part7Length : (target7Region2.map Setup.Block.length).sum = 768 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target7Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨31, by decide +kernel⟩).2

theorem checkedRegion3Part7Length : (target7Region3.map Setup.Block.length).sum = 20288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target7Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨32, by decide +kernel⟩).2

theorem checkedRegion3Part8Length : (target8Region3.map Setup.Block.length).sum = 1460 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target8Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨33, by decide +kernel⟩).2

theorem checkedRegion3Part9Length : (target9Region3.map Setup.Block.length).sum = 2700 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target9Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨34, by decide +kernel⟩).2

theorem checkedRegion3Part10Length : (target10Region3.map Setup.Block.length).sum = 16000 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target10Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨35, by decide +kernel⟩).2

theorem checkedRegion3Part11Length : (target11Region3.map Setup.Block.length).sum = 3040 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target11Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨36, by decide +kernel⟩).2

theorem checkedRegion3Part12Length : (target12Region3.map Setup.Block.length).sum = 1488 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target12Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨37, by decide +kernel⟩).2

theorem checkedRegion3Part13Length : (target13Region3.map Setup.Block.length).sum = 19280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target13Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨38, by decide +kernel⟩).2

theorem checkedRegion3Part14Length : (target14Region3.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target14Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨39, by decide +kernel⟩).2

theorem checkedRegion4Part14Length : (target14Region4.map Setup.Block.length).sum = 20160 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target14Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨40, by decide +kernel⟩).2

theorem checkedRegion4Part15Length : (target15Region4.map Setup.Block.length).sum = 1580 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target15Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨41, by decide +kernel⟩).2

theorem checkedRegion4Part16Length : (target16Region4.map Setup.Block.length).sum = 2644 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target16Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨42, by decide +kernel⟩).2

theorem checkedRegion4Part17Length : (target17Region4.map Setup.Block.length).sum = 15808 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target17Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨43, by decide +kernel⟩).2

theorem checkedRegion4Part18Length : (target18Region4.map Setup.Block.length).sum = 3280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target18Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨44, by decide +kernel⟩).2

theorem checkedRegion4Part19Length : (target19Region4.map Setup.Block.length).sum = 1472 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target19Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨45, by decide +kernel⟩).2

theorem checkedRegion4Part20Length : (target20Region4.map Setup.Block.length).sum = 18800 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target20Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨46, by decide +kernel⟩).2

theorem checkedRegion4Part21Length : (target21Region4.map Setup.Block.length).sum = 1792 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target21Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨47, by decide +kernel⟩).2

theorem checkedRegion5Part21Length : (target21Region5.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target21Region5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨48, by decide +kernel⟩).2

theorem checkedRegion6Part21Length : (target21Region6.map Setup.Block.length).sum = 262144 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column2.target21Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column2.facts ⟨49, by decide +kernel⟩).2

end Airbender.Compiler.ShiftPrefixNative.Column2
