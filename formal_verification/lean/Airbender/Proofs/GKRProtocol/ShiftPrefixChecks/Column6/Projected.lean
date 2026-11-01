import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column6.Certificate

namespace Airbender.Compiler.ShiftPrefixNative.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source0_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨0, by decide +kernel⟩).1

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 264563 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨0, by decide +kernel⟩).2

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source1_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨1, by decide +kernel⟩).1

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 1568 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨1, by decide +kernel⟩).2

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source2_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨2, by decide +kernel⟩).1

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 1528 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨2, by decide +kernel⟩).2

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source3_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨3, by decide +kernel⟩).1

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 1520 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨3, by decide +kernel⟩).2

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source4_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨4, by decide +kernel⟩).1

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 1344 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨4, by decide +kernel⟩).2

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source5_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨5, by decide +kernel⟩).1

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 1488 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨5, by decide +kernel⟩).2

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source6_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨6, by decide +kernel⟩).1

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨6, by decide +kernel⟩).2

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source7_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target7_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨7, by decide +kernel⟩).1

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source7_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨7, by decide +kernel⟩).2

theorem chunkChecked8 : normalizeSetupBlocks original8 = normalizeSetupBlocks target8 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source8_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target8_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨8, by decide +kernel⟩).1

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 1480 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source8_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨8, by decide +kernel⟩).2

theorem chunkChecked9 : normalizeSetupBlocks original9 = normalizeSetupBlocks target9 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source9_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target9_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨9, by decide +kernel⟩).1

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source9_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨9, by decide +kernel⟩).2

theorem chunkChecked10 : normalizeSetupBlocks original10 = normalizeSetupBlocks target10 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source10_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target10_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨10, by decide +kernel⟩).1

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source10_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨10, by decide +kernel⟩).2

theorem chunkChecked11 : normalizeSetupBlocks original11 = normalizeSetupBlocks target11 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source11_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target11_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨11, by decide +kernel⟩).1

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 1448 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source11_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨11, by decide +kernel⟩).2

theorem chunkChecked12 : normalizeSetupBlocks original12 = normalizeSetupBlocks target12 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source12_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target12_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨12, by decide +kernel⟩).1

theorem chunkLength12 : (original12.map Setup.Block.length).sum = 1120 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source12_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨12, by decide +kernel⟩).2

theorem chunkChecked13 : normalizeSetupBlocks original13 = normalizeSetupBlocks target13 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source13_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target13_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨13, by decide +kernel⟩).1

theorem chunkLength13 : (original13.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source13_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨13, by decide +kernel⟩).2

theorem chunkChecked14 : normalizeSetupBlocks original14 = normalizeSetupBlocks target14 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source14_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target14_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨14, by decide +kernel⟩).1

theorem chunkLength14 : (original14.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source14_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨14, by decide +kernel⟩).2

theorem chunkChecked15 : normalizeSetupBlocks original15 = normalizeSetupBlocks target15 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source15_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target15_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨15, by decide +kernel⟩).1

theorem chunkLength15 : (original15.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source15_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨15, by decide +kernel⟩).2

theorem chunkChecked16 : normalizeSetupBlocks original16 = normalizeSetupBlocks target16 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source16_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target16_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨16, by decide +kernel⟩).1

theorem chunkLength16 : (original16.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source16_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨16, by decide +kernel⟩).2

theorem chunkChecked17 : normalizeSetupBlocks original17 = normalizeSetupBlocks target17 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source17_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target17_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨17, by decide +kernel⟩).1

theorem chunkLength17 : (original17.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source17_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨17, by decide +kernel⟩).2

theorem chunkChecked18 : normalizeSetupBlocks original18 = normalizeSetupBlocks target18 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source18_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target18_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨18, by decide +kernel⟩).1

theorem chunkLength18 : (original18.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source18_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨18, by decide +kernel⟩).2

theorem chunkChecked19 : normalizeSetupBlocks original19 = normalizeSetupBlocks target19 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source19_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target19_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨19, by decide +kernel⟩).1

theorem chunkLength19 : (original19.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source19_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨19, by decide +kernel⟩).2

theorem chunkChecked20 : normalizeSetupBlocks original20 = normalizeSetupBlocks target20 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source20_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target20_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨20, by decide +kernel⟩).1

theorem chunkLength20 : (original20.map Setup.Block.length).sum = 1288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source20_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨20, by decide +kernel⟩).2

theorem chunkChecked21 : normalizeSetupBlocks original21 = normalizeSetupBlocks target21 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source21_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target21_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨21, by decide +kernel⟩).1

theorem chunkLength21 : (original21.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source21_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨21, by decide +kernel⟩).2

theorem chunkChecked22 : normalizeSetupBlocks original22 = normalizeSetupBlocks target22 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source22_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target22_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨22, by decide +kernel⟩).1

theorem chunkLength22 : (original22.map Setup.Block.length).sum = 1272 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source22_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨22, by decide +kernel⟩).2

theorem chunkChecked23 : normalizeSetupBlocks original23 = normalizeSetupBlocks target23 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source23_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target23_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨23, by decide +kernel⟩).1

theorem chunkLength23 : (original23.map Setup.Block.length).sum = 1112 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source23_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨23, by decide +kernel⟩).2

theorem chunkChecked24 : normalizeSetupBlocks original24 = normalizeSetupBlocks target24 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source24_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target24_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨24, by decide +kernel⟩).1

theorem chunkLength24 : (original24.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source24_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨24, by decide +kernel⟩).2

theorem chunkChecked25 : normalizeSetupBlocks original25 = normalizeSetupBlocks target25 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source25_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target25_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨25, by decide +kernel⟩).1

theorem chunkLength25 : (original25.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source25_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨25, by decide +kernel⟩).2

theorem chunkChecked26 : normalizeSetupBlocks original26 = normalizeSetupBlocks target26 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source26_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target26_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨26, by decide +kernel⟩).1

theorem chunkLength26 : (original26.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source26_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨26, by decide +kernel⟩).2

theorem chunkChecked27 : normalizeSetupBlocks original27 = normalizeSetupBlocks target27 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source27_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target27_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨27, by decide +kernel⟩).1

theorem chunkLength27 : (original27.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source27_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨27, by decide +kernel⟩).2

theorem chunkChecked28 : normalizeSetupBlocks original28 = normalizeSetupBlocks target28 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source28_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target28_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨28, by decide +kernel⟩).1

theorem chunkLength28 : (original28.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source28_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨28, by decide +kernel⟩).2

theorem chunkChecked29 : normalizeSetupBlocks original29 = normalizeSetupBlocks target29 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source29_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target29_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨29, by decide +kernel⟩).1

theorem chunkLength29 : (original29.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source29_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨29, by decide +kernel⟩).2

theorem chunkChecked30 : normalizeSetupBlocks original30 = normalizeSetupBlocks target30 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source30_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target30_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨30, by decide +kernel⟩).1

theorem chunkLength30 : (original30.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source30_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨30, by decide +kernel⟩).2

theorem chunkChecked31 : normalizeSetupBlocks original31 = normalizeSetupBlocks target31 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source31_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target31_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨31, by decide +kernel⟩).1

theorem chunkLength31 : (original31.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source31_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨31, by decide +kernel⟩).2

theorem chunkChecked32 : normalizeSetupBlocks original32 = normalizeSetupBlocks target32 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source32_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target32_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨32, by decide +kernel⟩).1

theorem chunkLength32 : (original32.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source32_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨32, by decide +kernel⟩).2

theorem chunkChecked33 : normalizeSetupBlocks original33 = normalizeSetupBlocks target33 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source33_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target33_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨33, by decide +kernel⟩).1

theorem chunkLength33 : (original33.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source33_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨33, by decide +kernel⟩).2

theorem chunkChecked34 : normalizeSetupBlocks original34 = normalizeSetupBlocks target34 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source34_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target34_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨34, by decide +kernel⟩).1

theorem chunkLength34 : (original34.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source34_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨34, by decide +kernel⟩).2

theorem chunkChecked35 : normalizeSetupBlocks original35 = normalizeSetupBlocks target35 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source35_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target35_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨35, by decide +kernel⟩).1

theorem chunkLength35 : (original35.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source35_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨35, by decide +kernel⟩).2

theorem chunkChecked36 : normalizeSetupBlocks original36 = normalizeSetupBlocks target36 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source36_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target36_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨36, by decide +kernel⟩).1

theorem chunkLength36 : (original36.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source36_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨36, by decide +kernel⟩).2

theorem chunkChecked37 : normalizeSetupBlocks original37 = normalizeSetupBlocks target37 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source37_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target37_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨37, by decide +kernel⟩).1

theorem chunkLength37 : (original37.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source37_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨37, by decide +kernel⟩).2

theorem chunkChecked38 : normalizeSetupBlocks original38 = normalizeSetupBlocks target38 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source38_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target38_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨38, by decide +kernel⟩).1

theorem chunkLength38 : (original38.map Setup.Block.length).sum = 1248 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source38_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨38, by decide +kernel⟩).2

theorem chunkChecked39 : normalizeSetupBlocks original39 = normalizeSetupBlocks target39 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source39_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target39_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨39, by decide +kernel⟩).1

theorem chunkLength39 : (original39.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source39_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨39, by decide +kernel⟩).2

theorem chunkChecked40 : normalizeSetupBlocks original40 = normalizeSetupBlocks target40 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source40_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target40_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨40, by decide +kernel⟩).1

theorem chunkLength40 : (original40.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source40_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨40, by decide +kernel⟩).2

theorem chunkChecked41 : normalizeSetupBlocks original41 = normalizeSetupBlocks target41 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source41_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target41_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨41, by decide +kernel⟩).1

theorem chunkLength41 : (original41.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source41_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨41, by decide +kernel⟩).2

theorem chunkChecked42 : normalizeSetupBlocks original42 = normalizeSetupBlocks target42 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source42_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target42_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨42, by decide +kernel⟩).1

theorem chunkLength42 : (original42.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source42_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨42, by decide +kernel⟩).2

theorem chunkChecked43 : normalizeSetupBlocks original43 = normalizeSetupBlocks target43 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source43_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target43_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨43, by decide +kernel⟩).1

theorem chunkLength43 : (original43.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source43_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨43, by decide +kernel⟩).2

theorem chunkChecked44 : normalizeSetupBlocks original44 = normalizeSetupBlocks target44 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source44_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target44_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨44, by decide +kernel⟩).1

theorem chunkLength44 : (original44.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source44_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨44, by decide +kernel⟩).2

theorem chunkChecked45 : normalizeSetupBlocks original45 = normalizeSetupBlocks target45 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source45_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target45_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨45, by decide +kernel⟩).1

theorem chunkLength45 : (original45.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source45_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨45, by decide +kernel⟩).2

theorem chunkChecked46 : normalizeSetupBlocks original46 = normalizeSetupBlocks target46 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source46_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target46_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨46, by decide +kernel⟩).1

theorem chunkLength46 : (original46.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source46_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨46, by decide +kernel⟩).2

theorem chunkChecked47 : normalizeSetupBlocks original47 = normalizeSetupBlocks target47 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source47_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target47_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨47, by decide +kernel⟩).1

theorem chunkLength47 : (original47.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source47_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨47, by decide +kernel⟩).2

theorem chunkChecked48 : normalizeSetupBlocks original48 = normalizeSetupBlocks target48 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source48_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target48_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨48, by decide +kernel⟩).1

theorem chunkLength48 : (original48.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source48_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨48, by decide +kernel⟩).2

theorem chunkChecked49 : normalizeSetupBlocks original49 = normalizeSetupBlocks target49 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source49_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target49_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨49, by decide +kernel⟩).1

theorem chunkLength49 : (original49.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source49_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨49, by decide +kernel⟩).2

theorem chunkChecked50 : normalizeSetupBlocks original50 = normalizeSetupBlocks target50 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source50_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target50_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨50, by decide +kernel⟩).1

theorem chunkLength50 : (original50.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source50_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨50, by decide +kernel⟩).2

theorem chunkChecked51 : normalizeSetupBlocks original51 = normalizeSetupBlocks target51 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source51_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target51_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨51, by decide +kernel⟩).1

theorem chunkLength51 : (original51.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source51_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨51, by decide +kernel⟩).2

theorem chunkChecked52 : normalizeSetupBlocks original52 = normalizeSetupBlocks target52 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source52_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target52_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨52, by decide +kernel⟩).1

theorem chunkLength52 : (original52.map Setup.Block.length).sum = 1944 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source52_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨52, by decide +kernel⟩).2

theorem chunkChecked53 : normalizeSetupBlocks original53 = normalizeSetupBlocks target53 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source53_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target53_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨53, by decide +kernel⟩).1

theorem chunkLength53 : (original53.map Setup.Block.length).sum = 1520 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source53_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨53, by decide +kernel⟩).2

theorem chunkChecked54 : normalizeSetupBlocks original54 = normalizeSetupBlocks target54 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source54_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target54_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨54, by decide +kernel⟩).1

theorem chunkLength54 : (original54.map Setup.Block.length).sum = 1328 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source54_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨54, by decide +kernel⟩).2

theorem chunkChecked55 : normalizeSetupBlocks original55 = normalizeSetupBlocks target55 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source55_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target55_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨55, by decide +kernel⟩).1

theorem chunkLength55 : (original55.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source55_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨55, by decide +kernel⟩).2

theorem chunkChecked56 : normalizeSetupBlocks original56 = normalizeSetupBlocks target56 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source56_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target56_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨56, by decide +kernel⟩).1

theorem chunkLength56 : (original56.map Setup.Block.length).sum = 1472 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source56_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨56, by decide +kernel⟩).2

theorem chunkChecked57 : normalizeSetupBlocks original57 = normalizeSetupBlocks target57 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source57_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target57_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨57, by decide +kernel⟩).1

theorem chunkLength57 : (original57.map Setup.Block.length).sum = 1296 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source57_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨57, by decide +kernel⟩).2

theorem chunkChecked58 : normalizeSetupBlocks original58 = normalizeSetupBlocks target58 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source58_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target58_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨58, by decide +kernel⟩).1

theorem chunkLength58 : (original58.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source58_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨58, by decide +kernel⟩).2

theorem chunkChecked59 : normalizeSetupBlocks original59 = normalizeSetupBlocks target59 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source59_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target59_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨59, by decide +kernel⟩).1

theorem chunkLength59 : (original59.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source59_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨59, by decide +kernel⟩).2

theorem chunkChecked60 : normalizeSetupBlocks original60 = normalizeSetupBlocks target60 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source60_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target60_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨60, by decide +kernel⟩).1

theorem chunkLength60 : (original60.map Setup.Block.length).sum = 1288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source60_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨60, by decide +kernel⟩).2

theorem chunkChecked61 : normalizeSetupBlocks original61 = normalizeSetupBlocks target61 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source61_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target61_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨61, by decide +kernel⟩).1

theorem chunkLength61 : (original61.map Setup.Block.length).sum = 1244 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source61_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨61, by decide +kernel⟩).2

theorem chunkChecked62 : normalizeSetupBlocks original62 = normalizeSetupBlocks target62 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source62_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target62_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨62, by decide +kernel⟩).1

theorem chunkLength62 : (original62.map Setup.Block.length).sum = 1132 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source62_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨62, by decide +kernel⟩).2

theorem chunkChecked63 : normalizeSetupBlocks original63 = normalizeSetupBlocks target63 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source63_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target63_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨63, by decide +kernel⟩).1

theorem chunkLength63 : (original63.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source63_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨63, by decide +kernel⟩).2

theorem chunkChecked64 : normalizeSetupBlocks original64 = normalizeSetupBlocks target64 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source64_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target64_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨64, by decide +kernel⟩).1

theorem chunkLength64 : (original64.map Setup.Block.length).sum = 1248 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source64_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨64, by decide +kernel⟩).2

theorem chunkChecked65 : normalizeSetupBlocks original65 = normalizeSetupBlocks target65 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source65_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target65_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨65, by decide +kernel⟩).1

theorem chunkLength65 : (original65.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source65_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨65, by decide +kernel⟩).2

theorem chunkChecked66 : normalizeSetupBlocks original66 = normalizeSetupBlocks target66 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source66_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target66_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨66, by decide +kernel⟩).1

theorem chunkLength66 : (original66.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source66_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨66, by decide +kernel⟩).2

theorem chunkChecked67 : normalizeSetupBlocks original67 = normalizeSetupBlocks target67 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source67_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target67_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨67, by decide +kernel⟩).1

theorem chunkLength67 : (original67.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source67_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨67, by decide +kernel⟩).2

theorem chunkChecked68 : normalizeSetupBlocks original68 = normalizeSetupBlocks target68 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source68_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target68_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨68, by decide +kernel⟩).1

theorem chunkLength68 : (original68.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source68_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨68, by decide +kernel⟩).2

theorem chunkChecked69 : normalizeSetupBlocks original69 = normalizeSetupBlocks target69 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source69_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target69_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨69, by decide +kernel⟩).1

theorem chunkLength69 : (original69.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source69_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨69, by decide +kernel⟩).2

theorem chunkChecked70 : normalizeSetupBlocks original70 = normalizeSetupBlocks target70 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source70_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target70_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨70, by decide +kernel⟩).1

theorem chunkLength70 : (original70.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source70_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨70, by decide +kernel⟩).2

theorem chunkChecked71 : normalizeSetupBlocks original71 = normalizeSetupBlocks target71 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source71_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target71_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨71, by decide +kernel⟩).1

theorem chunkLength71 : (original71.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source71_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨71, by decide +kernel⟩).2

theorem chunkChecked72 : normalizeSetupBlocks original72 = normalizeSetupBlocks target72 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source72_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target72_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨72, by decide +kernel⟩).1

theorem chunkLength72 : (original72.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source72_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨72, by decide +kernel⟩).2

theorem chunkChecked73 : normalizeSetupBlocks original73 = normalizeSetupBlocks target73 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source73_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target73_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨73, by decide +kernel⟩).1

theorem chunkLength73 : (original73.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source73_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨73, by decide +kernel⟩).2

theorem chunkChecked74 : normalizeSetupBlocks original74 = normalizeSetupBlocks target74 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source74_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target74_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨74, by decide +kernel⟩).1

theorem chunkLength74 : (original74.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source74_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨74, by decide +kernel⟩).2

theorem chunkChecked75 : normalizeSetupBlocks original75 = normalizeSetupBlocks target75 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source75_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target75_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨75, by decide +kernel⟩).1

theorem chunkLength75 : (original75.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source75_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨75, by decide +kernel⟩).2

theorem chunkChecked76 : normalizeSetupBlocks original76 = normalizeSetupBlocks target76 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source76_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target76_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨76, by decide +kernel⟩).1

theorem chunkLength76 : (original76.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source76_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨76, by decide +kernel⟩).2

theorem chunkChecked77 : normalizeSetupBlocks original77 = normalizeSetupBlocks target77 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source77_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target77_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨77, by decide +kernel⟩).1

theorem chunkLength77 : (original77.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source77_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨77, by decide +kernel⟩).2

theorem chunkChecked78 : normalizeSetupBlocks original78 = normalizeSetupBlocks target78 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source78_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target78_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨78, by decide +kernel⟩).1

theorem chunkLength78 : (original78.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source78_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨78, by decide +kernel⟩).2

theorem chunkChecked79 : normalizeSetupBlocks original79 = normalizeSetupBlocks target79 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source79_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target79_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨79, by decide +kernel⟩).1

theorem chunkLength79 : (original79.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source79_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨79, by decide +kernel⟩).2

theorem chunkChecked80 : normalizeSetupBlocks original80 = normalizeSetupBlocks target80 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source80_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target80_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨80, by decide +kernel⟩).1

theorem chunkLength80 : (original80.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source80_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨80, by decide +kernel⟩).2

theorem chunkChecked81 : normalizeSetupBlocks original81 = normalizeSetupBlocks target81 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source81_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target81_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨81, by decide +kernel⟩).1

theorem chunkLength81 : (original81.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source81_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨81, by decide +kernel⟩).2

theorem chunkChecked82 : normalizeSetupBlocks original82 = normalizeSetupBlocks target82 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source82_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target82_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨82, by decide +kernel⟩).1

theorem chunkLength82 : (original82.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source82_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨82, by decide +kernel⟩).2

theorem chunkChecked83 : normalizeSetupBlocks original83 = normalizeSetupBlocks target83 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source83_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target83_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨83, by decide +kernel⟩).1

theorem chunkLength83 : (original83.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source83_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨83, by decide +kernel⟩).2

theorem chunkChecked84 : normalizeSetupBlocks original84 = normalizeSetupBlocks target84 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source84_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target84_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨84, by decide +kernel⟩).1

theorem chunkLength84 : (original84.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source84_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨84, by decide +kernel⟩).2

theorem chunkChecked85 : normalizeSetupBlocks original85 = normalizeSetupBlocks target85 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source85_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target85_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨85, by decide +kernel⟩).1

theorem chunkLength85 : (original85.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source85_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨85, by decide +kernel⟩).2

theorem chunkChecked86 : normalizeSetupBlocks original86 = normalizeSetupBlocks target86 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source86_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target86_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨86, by decide +kernel⟩).1

theorem chunkLength86 : (original86.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source86_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨86, by decide +kernel⟩).2

theorem chunkChecked87 : normalizeSetupBlocks original87 = normalizeSetupBlocks target87 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source87_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target87_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨87, by decide +kernel⟩).1

theorem chunkLength87 : (original87.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source87_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨87, by decide +kernel⟩).2

theorem chunkChecked88 : normalizeSetupBlocks original88 = normalizeSetupBlocks target88 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source88_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target88_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨88, by decide +kernel⟩).1

theorem chunkLength88 : (original88.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source88_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨88, by decide +kernel⟩).2

theorem chunkChecked89 : normalizeSetupBlocks original89 = normalizeSetupBlocks target89 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source89_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target89_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨89, by decide +kernel⟩).1

theorem chunkLength89 : (original89.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source89_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨89, by decide +kernel⟩).2

theorem chunkChecked90 : normalizeSetupBlocks original90 = normalizeSetupBlocks target90 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source90_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target90_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨90, by decide +kernel⟩).1

theorem chunkLength90 : (original90.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source90_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨90, by decide +kernel⟩).2

theorem chunkChecked91 : normalizeSetupBlocks original91 = normalizeSetupBlocks target91 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source91_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target91_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨91, by decide +kernel⟩).1

theorem chunkLength91 : (original91.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source91_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨91, by decide +kernel⟩).2

theorem chunkChecked92 : normalizeSetupBlocks original92 = normalizeSetupBlocks target92 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source92_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target92_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨92, by decide +kernel⟩).1

theorem chunkLength92 : (original92.map Setup.Block.length).sum = 1248 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source92_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨92, by decide +kernel⟩).2

theorem chunkChecked93 : normalizeSetupBlocks original93 = normalizeSetupBlocks target93 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source93_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target93_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨93, by decide +kernel⟩).1

theorem chunkLength93 : (original93.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source93_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨93, by decide +kernel⟩).2

theorem chunkChecked94 : normalizeSetupBlocks original94 = normalizeSetupBlocks target94 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source94_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target94_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨94, by decide +kernel⟩).1

theorem chunkLength94 : (original94.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source94_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨94, by decide +kernel⟩).2

theorem chunkChecked95 : normalizeSetupBlocks original95 = normalizeSetupBlocks target95 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source95_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target95_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨95, by decide +kernel⟩).1

theorem chunkLength95 : (original95.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source95_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨95, by decide +kernel⟩).2

theorem chunkChecked96 : normalizeSetupBlocks original96 = normalizeSetupBlocks target96 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source96_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target96_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨96, by decide +kernel⟩).1

theorem chunkLength96 : (original96.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source96_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨96, by decide +kernel⟩).2

theorem chunkChecked97 : normalizeSetupBlocks original97 = normalizeSetupBlocks target97 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source97_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target97_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨97, by decide +kernel⟩).1

theorem chunkLength97 : (original97.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source97_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨97, by decide +kernel⟩).2

theorem chunkChecked98 : normalizeSetupBlocks original98 = normalizeSetupBlocks target98 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source98_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target98_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨98, by decide +kernel⟩).1

theorem chunkLength98 : (original98.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source98_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨98, by decide +kernel⟩).2

theorem chunkChecked99 : normalizeSetupBlocks original99 = normalizeSetupBlocks target99 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source99_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target99_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨99, by decide +kernel⟩).1

theorem chunkLength99 : (original99.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source99_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨99, by decide +kernel⟩).2

theorem chunkChecked100 : normalizeSetupBlocks original100 = normalizeSetupBlocks target100 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source100_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target100_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨100, by decide +kernel⟩).1

theorem chunkLength100 : (original100.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source100_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨100, by decide +kernel⟩).2

theorem chunkChecked101 : normalizeSetupBlocks original101 = normalizeSetupBlocks target101 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source101_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target101_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨101, by decide +kernel⟩).1

theorem chunkLength101 : (original101.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source101_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨101, by decide +kernel⟩).2

theorem chunkChecked102 : normalizeSetupBlocks original102 = normalizeSetupBlocks target102 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source102_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target102_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨102, by decide +kernel⟩).1

theorem chunkLength102 : (original102.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source102_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨102, by decide +kernel⟩).2

theorem chunkChecked103 : normalizeSetupBlocks original103 = normalizeSetupBlocks target103 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source103_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target103_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨103, by decide +kernel⟩).1

theorem chunkLength103 : (original103.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source103_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨103, by decide +kernel⟩).2

theorem chunkChecked104 : normalizeSetupBlocks original104 = normalizeSetupBlocks target104 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source104_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target104_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨104, by decide +kernel⟩).1

theorem chunkLength104 : (original104.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source104_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨104, by decide +kernel⟩).2

theorem chunkChecked105 : normalizeSetupBlocks original105 = normalizeSetupBlocks target105 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source105_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target105_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨105, by decide +kernel⟩).1

theorem chunkLength105 : (original105.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source105_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨105, by decide +kernel⟩).2

theorem chunkChecked106 : normalizeSetupBlocks original106 = normalizeSetupBlocks target106 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source106_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target106_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨106, by decide +kernel⟩).1

theorem chunkLength106 : (original106.map Setup.Block.length).sum = 2490 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source106_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨106, by decide +kernel⟩).2

theorem chunkChecked107 : normalizeSetupBlocks original107 = normalizeSetupBlocks target107 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source107_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target107_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨107, by decide +kernel⟩).1

theorem chunkLength107 : (original107.map Setup.Block.length).sum = 2296 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source107_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨107, by decide +kernel⟩).2

theorem chunkChecked108 : normalizeSetupBlocks original108 = normalizeSetupBlocks target108 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source108_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target108_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨108, by decide +kernel⟩).1

theorem chunkLength108 : (original108.map Setup.Block.length).sum = 2304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source108_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨108, by decide +kernel⟩).2

theorem chunkChecked109 : normalizeSetupBlocks original109 = normalizeSetupBlocks target109 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source109_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target109_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨109, by decide +kernel⟩).1

theorem chunkLength109 : (original109.map Setup.Block.length).sum = 2094 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source109_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨109, by decide +kernel⟩).2

theorem chunkChecked110 : normalizeSetupBlocks original110 = normalizeSetupBlocks target110 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source110_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target110_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨110, by decide +kernel⟩).1

theorem chunkLength110 : (original110.map Setup.Block.length).sum = 2290 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source110_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨110, by decide +kernel⟩).2

theorem chunkChecked111 : normalizeSetupBlocks original111 = normalizeSetupBlocks target111 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source111_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target111_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨111, by decide +kernel⟩).1

theorem chunkLength111 : (original111.map Setup.Block.length).sum = 2304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source111_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨111, by decide +kernel⟩).2

theorem chunkChecked112 : normalizeSetupBlocks original112 = normalizeSetupBlocks target112 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source112_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target112_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨112, by decide +kernel⟩).1

theorem chunkLength112 : (original112.map Setup.Block.length).sum = 2288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source112_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨112, by decide +kernel⟩).2

theorem chunkChecked113 : normalizeSetupBlocks original113 = normalizeSetupBlocks target113 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source113_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target113_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨113, by decide +kernel⟩).1

theorem chunkLength113 : (original113.map Setup.Block.length).sum = 2080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source113_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨113, by decide +kernel⟩).2

theorem chunkChecked114 : normalizeSetupBlocks original114 = normalizeSetupBlocks target114 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source114_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target114_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨114, by decide +kernel⟩).1

theorem chunkLength114 : (original114.map Setup.Block.length).sum = 2280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source114_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨114, by decide +kernel⟩).2

theorem chunkChecked115 : normalizeSetupBlocks original115 = normalizeSetupBlocks target115 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source115_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target115_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨115, by decide +kernel⟩).1

theorem chunkLength115 : (original115.map Setup.Block.length).sum = 2078 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source115_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨115, by decide +kernel⟩).2

theorem chunkChecked116 : normalizeSetupBlocks original116 = normalizeSetupBlocks target116 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source116_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target116_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨116, by decide +kernel⟩).1

theorem chunkLength116 : (original116.map Setup.Block.length).sum = 2274 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source116_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨116, by decide +kernel⟩).2

theorem chunkChecked117 : normalizeSetupBlocks original117 = normalizeSetupBlocks target117 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source117_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target117_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨117, by decide +kernel⟩).1

theorem chunkLength117 : (original117.map Setup.Block.length).sum = 2280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source117_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨117, by decide +kernel⟩).2

theorem chunkChecked118 : normalizeSetupBlocks original118 = normalizeSetupBlocks target118 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source118_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target118_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨118, by decide +kernel⟩).1

theorem chunkLength118 : (original118.map Setup.Block.length).sum = 2080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source118_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨118, by decide +kernel⟩).2

theorem chunkChecked119 : normalizeSetupBlocks original119 = normalizeSetupBlocks target119 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source119_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target119_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨119, by decide +kernel⟩).1

theorem chunkLength119 : (original119.map Setup.Block.length).sum = 2272 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source119_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨119, by decide +kernel⟩).2

theorem chunkChecked120 : normalizeSetupBlocks original120 = normalizeSetupBlocks target120 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source120_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target120_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨120, by decide +kernel⟩).1

theorem chunkLength120 : (original120.map Setup.Block.length).sum = 2072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source120_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨120, by decide +kernel⟩).2

theorem chunkChecked121 : normalizeSetupBlocks original121 = normalizeSetupBlocks target121 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source121_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target121_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨121, by decide +kernel⟩).1

theorem chunkLength121 : (original121.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source121_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨121, by decide +kernel⟩).2

theorem chunkChecked122 : normalizeSetupBlocks original122 = normalizeSetupBlocks target122 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source122_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target122_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨122, by decide +kernel⟩).1

theorem chunkLength122 : (original122.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source122_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨122, by decide +kernel⟩).2

theorem chunkChecked123 : normalizeSetupBlocks original123 = normalizeSetupBlocks target123 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source123_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target123_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨123, by decide +kernel⟩).1

theorem chunkLength123 : (original123.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source123_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨123, by decide +kernel⟩).2

theorem chunkChecked124 : normalizeSetupBlocks original124 = normalizeSetupBlocks target124 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source124_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target124_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨124, by decide +kernel⟩).1

theorem chunkLength124 : (original124.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source124_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨124, by decide +kernel⟩).2

theorem chunkChecked125 : normalizeSetupBlocks original125 = normalizeSetupBlocks target125 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source125_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target125_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨125, by decide +kernel⟩).1

theorem chunkLength125 : (original125.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source125_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨125, by decide +kernel⟩).2

theorem chunkChecked126 : normalizeSetupBlocks original126 = normalizeSetupBlocks target126 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source126_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target126_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨126, by decide +kernel⟩).1

theorem chunkLength126 : (original126.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source126_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨126, by decide +kernel⟩).2

theorem chunkChecked127 : normalizeSetupBlocks original127 = normalizeSetupBlocks target127 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source127_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target127_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨127, by decide +kernel⟩).1

theorem chunkLength127 : (original127.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source127_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨127, by decide +kernel⟩).2

theorem chunkChecked128 : normalizeSetupBlocks original128 = normalizeSetupBlocks target128 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source128_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target128_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨128, by decide +kernel⟩).1

theorem chunkLength128 : (original128.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source128_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨128, by decide +kernel⟩).2

theorem chunkChecked129 : normalizeSetupBlocks original129 = normalizeSetupBlocks target129 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source129_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target129_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨129, by decide +kernel⟩).1

theorem chunkLength129 : (original129.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source129_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨129, by decide +kernel⟩).2

theorem chunkChecked130 : normalizeSetupBlocks original130 = normalizeSetupBlocks target130 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source130_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target130_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨130, by decide +kernel⟩).1

theorem chunkLength130 : (original130.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source130_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨130, by decide +kernel⟩).2

theorem chunkChecked131 : normalizeSetupBlocks original131 = normalizeSetupBlocks target131 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source131_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target131_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨131, by decide +kernel⟩).1

theorem chunkLength131 : (original131.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source131_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨131, by decide +kernel⟩).2

theorem chunkChecked132 : normalizeSetupBlocks original132 = normalizeSetupBlocks target132 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source132_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target132_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨132, by decide +kernel⟩).1

theorem chunkLength132 : (original132.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source132_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨132, by decide +kernel⟩).2

theorem chunkChecked133 : normalizeSetupBlocks original133 = normalizeSetupBlocks target133 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source133_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target133_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨133, by decide +kernel⟩).1

theorem chunkLength133 : (original133.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source133_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨133, by decide +kernel⟩).2

theorem chunkChecked134 : normalizeSetupBlocks original134 = normalizeSetupBlocks target134 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source134_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target134_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨134, by decide +kernel⟩).1

theorem chunkLength134 : (original134.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source134_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨134, by decide +kernel⟩).2

theorem chunkChecked135 : normalizeSetupBlocks original135 = normalizeSetupBlocks target135 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source135_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target135_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨135, by decide +kernel⟩).1

theorem chunkLength135 : (original135.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source135_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨135, by decide +kernel⟩).2

theorem chunkChecked136 : normalizeSetupBlocks original136 = normalizeSetupBlocks target136 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source136_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target136_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨136, by decide +kernel⟩).1

theorem chunkLength136 : (original136.map Setup.Block.length).sum = 2312 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source136_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨136, by decide +kernel⟩).2

theorem chunkChecked137 : normalizeSetupBlocks original137 = normalizeSetupBlocks target137 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source137_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target137_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨137, by decide +kernel⟩).1

theorem chunkLength137 : (original137.map Setup.Block.length).sum = 1792 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source137_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨137, by decide +kernel⟩).2

theorem chunkChecked138 : normalizeSetupBlocks original138 = normalizeSetupBlocks target138 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source138_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target138_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨138, by decide +kernel⟩).1

theorem chunkLength138 : (original138.map Setup.Block.length).sum = 1576 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source138_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨138, by decide +kernel⟩).2

theorem chunkChecked139 : normalizeSetupBlocks original139 = normalizeSetupBlocks target139 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source139_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target139_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨139, by decide +kernel⟩).1

theorem chunkLength139 : (original139.map Setup.Block.length).sum = 1504 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source139_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨139, by decide +kernel⟩).2

theorem chunkChecked140 : normalizeSetupBlocks original140 = normalizeSetupBlocks target140 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source140_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target140_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨140, by decide +kernel⟩).1

theorem chunkLength140 : (original140.map Setup.Block.length).sum = 1520 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source140_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨140, by decide +kernel⟩).2

theorem chunkChecked141 : normalizeSetupBlocks original141 = normalizeSetupBlocks target141 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source141_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target141_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨141, by decide +kernel⟩).1

theorem chunkLength141 : (original141.map Setup.Block.length).sum = 1352 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source141_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨141, by decide +kernel⟩).2

theorem chunkChecked142 : normalizeSetupBlocks original142 = normalizeSetupBlocks target142 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source142_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target142_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨142, by decide +kernel⟩).1

theorem chunkLength142 : (original142.map Setup.Block.length).sum = 1456 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source142_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨142, by decide +kernel⟩).2

theorem chunkChecked143 : normalizeSetupBlocks original143 = normalizeSetupBlocks target143 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source143_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target143_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨143, by decide +kernel⟩).1

theorem chunkLength143 : (original143.map Setup.Block.length).sum = 1320 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source143_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨143, by decide +kernel⟩).2

theorem chunkChecked144 : normalizeSetupBlocks original144 = normalizeSetupBlocks target144 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source144_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target144_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨144, by decide +kernel⟩).1

theorem chunkLength144 : (original144.map Setup.Block.length).sum = 1312 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source144_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨144, by decide +kernel⟩).2

theorem chunkChecked145 : normalizeSetupBlocks original145 = normalizeSetupBlocks target145 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source145_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target145_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨145, by decide +kernel⟩).1

theorem chunkLength145 : (original145.map Setup.Block.length).sum = 1456 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source145_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨145, by decide +kernel⟩).2

theorem chunkChecked146 : normalizeSetupBlocks original146 = normalizeSetupBlocks target146 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source146_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target146_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨146, by decide +kernel⟩).1

theorem chunkLength146 : (original146.map Setup.Block.length).sum = 1320 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source146_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨146, by decide +kernel⟩).2

theorem chunkChecked147 : normalizeSetupBlocks original147 = normalizeSetupBlocks target147 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source147_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target147_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨147, by decide +kernel⟩).1

theorem chunkLength147 : (original147.map Setup.Block.length).sum = 1320 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source147_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨147, by decide +kernel⟩).2

theorem chunkChecked148 : normalizeSetupBlocks original148 = normalizeSetupBlocks target148 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source148_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target148_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨148, by decide +kernel⟩).1

theorem chunkLength148 : (original148.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source148_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨148, by decide +kernel⟩).2

theorem chunkChecked149 : normalizeSetupBlocks original149 = normalizeSetupBlocks target149 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source149_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target149_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨149, by decide +kernel⟩).1

theorem chunkLength149 : (original149.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source149_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨149, by decide +kernel⟩).2

theorem chunkChecked150 : normalizeSetupBlocks original150 = normalizeSetupBlocks target150 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source150_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target150_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨150, by decide +kernel⟩).1

theorem chunkLength150 : (original150.map Setup.Block.length).sum = 1288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source150_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨150, by decide +kernel⟩).2

theorem chunkChecked151 : normalizeSetupBlocks original151 = normalizeSetupBlocks target151 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source151_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target151_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨151, by decide +kernel⟩).1

theorem chunkLength151 : (original151.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source151_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨151, by decide +kernel⟩).2

theorem chunkChecked152 : normalizeSetupBlocks original152 = normalizeSetupBlocks target152 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source152_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target152_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨152, by decide +kernel⟩).1

theorem chunkLength152 : (original152.map Setup.Block.length).sum = 1272 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source152_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨152, by decide +kernel⟩).2

theorem chunkChecked153 : normalizeSetupBlocks original153 = normalizeSetupBlocks target153 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source153_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target153_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨153, by decide +kernel⟩).1

theorem chunkLength153 : (original153.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source153_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨153, by decide +kernel⟩).2

theorem chunkChecked154 : normalizeSetupBlocks original154 = normalizeSetupBlocks target154 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source154_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target154_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨154, by decide +kernel⟩).1

theorem chunkLength154 : (original154.map Setup.Block.length).sum = 1296 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source154_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨154, by decide +kernel⟩).2

theorem chunkChecked155 : normalizeSetupBlocks original155 = normalizeSetupBlocks target155 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source155_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target155_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨155, by decide +kernel⟩).1

theorem chunkLength155 : (original155.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source155_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨155, by decide +kernel⟩).2

theorem chunkChecked156 : normalizeSetupBlocks original156 = normalizeSetupBlocks target156 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source156_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target156_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨156, by decide +kernel⟩).1

theorem chunkLength156 : (original156.map Setup.Block.length).sum = 1112 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source156_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨156, by decide +kernel⟩).2

theorem chunkChecked157 : normalizeSetupBlocks original157 = normalizeSetupBlocks target157 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source157_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target157_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨157, by decide +kernel⟩).1

theorem chunkLength157 : (original157.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source157_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨157, by decide +kernel⟩).2

theorem chunkChecked158 : normalizeSetupBlocks original158 = normalizeSetupBlocks target158 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source158_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target158_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨158, by decide +kernel⟩).1

theorem chunkLength158 : (original158.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source158_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨158, by decide +kernel⟩).2

theorem chunkChecked159 : normalizeSetupBlocks original159 = normalizeSetupBlocks target159 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source159_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target159_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨159, by decide +kernel⟩).1

theorem chunkLength159 : (original159.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source159_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨159, by decide +kernel⟩).2

theorem chunkChecked160 : normalizeSetupBlocks original160 = normalizeSetupBlocks target160 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source160_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target160_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨160, by decide +kernel⟩).1

theorem chunkLength160 : (original160.map Setup.Block.length).sum = 1286 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source160_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨160, by decide +kernel⟩).2

theorem chunkChecked161 : normalizeSetupBlocks original161 = normalizeSetupBlocks target161 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source161_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target161_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨161, by decide +kernel⟩).1

theorem chunkLength161 : (original161.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source161_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨161, by decide +kernel⟩).2

theorem chunkChecked162 : normalizeSetupBlocks original162 = normalizeSetupBlocks target162 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source162_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target162_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨162, by decide +kernel⟩).1

theorem chunkLength162 : (original162.map Setup.Block.length).sum = 1210 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source162_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨162, by decide +kernel⟩).2

theorem chunkChecked163 : normalizeSetupBlocks original163 = normalizeSetupBlocks target163 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source163_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target163_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨163, by decide +kernel⟩).1

theorem chunkLength163 : (original163.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source163_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨163, by decide +kernel⟩).2

theorem chunkChecked164 : normalizeSetupBlocks original164 = normalizeSetupBlocks target164 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source164_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target164_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨164, by decide +kernel⟩).1

theorem chunkLength164 : (original164.map Setup.Block.length).sum = 1214 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source164_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨164, by decide +kernel⟩).2

theorem chunkChecked165 : normalizeSetupBlocks original165 = normalizeSetupBlocks target165 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source165_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target165_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨165, by decide +kernel⟩).1

theorem chunkLength165 : (original165.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source165_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨165, by decide +kernel⟩).2

theorem chunkChecked166 : normalizeSetupBlocks original166 = normalizeSetupBlocks target166 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source166_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target166_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨166, by decide +kernel⟩).1

theorem chunkLength166 : (original166.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source166_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨166, by decide +kernel⟩).2

theorem chunkChecked167 : normalizeSetupBlocks original167 = normalizeSetupBlocks target167 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source167_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target167_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨167, by decide +kernel⟩).1

theorem chunkLength167 : (original167.map Setup.Block.length).sum = 1234 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source167_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨167, by decide +kernel⟩).2

theorem chunkChecked168 : normalizeSetupBlocks original168 = normalizeSetupBlocks target168 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source168_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target168_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨168, by decide +kernel⟩).1

theorem chunkLength168 : (original168.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source168_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨168, by decide +kernel⟩).2

theorem chunkChecked169 : normalizeSetupBlocks original169 = normalizeSetupBlocks target169 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source169_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target169_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨169, by decide +kernel⟩).1

theorem chunkLength169 : (original169.map Setup.Block.length).sum = 1206 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source169_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨169, by decide +kernel⟩).2

theorem chunkChecked170 : normalizeSetupBlocks original170 = normalizeSetupBlocks target170 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source170_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target170_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨170, by decide +kernel⟩).1

theorem chunkLength170 : (original170.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source170_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨170, by decide +kernel⟩).2

theorem chunkChecked171 : normalizeSetupBlocks original171 = normalizeSetupBlocks target171 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source171_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target171_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨171, by decide +kernel⟩).1

theorem chunkLength171 : (original171.map Setup.Block.length).sum = 1209 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source171_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨171, by decide +kernel⟩).2

theorem chunkChecked172 : normalizeSetupBlocks original172 = normalizeSetupBlocks target172 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source172_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target172_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨172, by decide +kernel⟩).1

theorem chunkLength172 : (original172.map Setup.Block.length).sum = 1073 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source172_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨172, by decide +kernel⟩).2

theorem chunkChecked173 : normalizeSetupBlocks original173 = normalizeSetupBlocks target173 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source173_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target173_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨173, by decide +kernel⟩).1

theorem chunkLength173 : (original173.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source173_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨173, by decide +kernel⟩).2

theorem chunkChecked174 : normalizeSetupBlocks original174 = normalizeSetupBlocks target174 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source174_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target174_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨174, by decide +kernel⟩).1

theorem chunkLength174 : (original174.map Setup.Block.length).sum = 1198 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source174_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨174, by decide +kernel⟩).2

theorem chunkChecked175 : normalizeSetupBlocks original175 = normalizeSetupBlocks target175 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source175_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target175_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨175, by decide +kernel⟩).1

theorem chunkLength175 : (original175.map Setup.Block.length).sum = 1096 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source175_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨175, by decide +kernel⟩).2

theorem chunkChecked176 : normalizeSetupBlocks original176 = normalizeSetupBlocks target176 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source176_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target176_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨176, by decide +kernel⟩).1

theorem chunkLength176 : (original176.map Setup.Block.length).sum = 1193 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source176_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨176, by decide +kernel⟩).2

theorem chunkChecked177 : normalizeSetupBlocks original177 = normalizeSetupBlocks target177 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source177_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target177_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨177, by decide +kernel⟩).1

theorem chunkLength177 : (original177.map Setup.Block.length).sum = 1089 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source177_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨177, by decide +kernel⟩).2

theorem chunkChecked178 : normalizeSetupBlocks original178 = normalizeSetupBlocks target178 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source178_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target178_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨178, by decide +kernel⟩).1

theorem chunkLength178 : (original178.map Setup.Block.length).sum = 1079 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source178_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨178, by decide +kernel⟩).2

theorem chunkChecked179 : normalizeSetupBlocks original179 = normalizeSetupBlocks target179 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source179_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target179_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨179, by decide +kernel⟩).1

theorem chunkLength179 : (original179.map Setup.Block.length).sum = 1199 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source179_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨179, by decide +kernel⟩).2

theorem chunkChecked180 : normalizeSetupBlocks original180 = normalizeSetupBlocks target180 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source180_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target180_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨180, by decide +kernel⟩).1

theorem chunkLength180 : (original180.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source180_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨180, by decide +kernel⟩).2

theorem chunkChecked181 : normalizeSetupBlocks original181 = normalizeSetupBlocks target181 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source181_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target181_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨181, by decide +kernel⟩).1

theorem chunkLength181 : (original181.map Setup.Block.length).sum = 1193 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source181_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨181, by decide +kernel⟩).2

theorem chunkChecked182 : normalizeSetupBlocks original182 = normalizeSetupBlocks target182 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source182_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target182_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨182, by decide +kernel⟩).1

theorem chunkLength182 : (original182.map Setup.Block.length).sum = 1097 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source182_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨182, by decide +kernel⟩).2

theorem chunkChecked183 : normalizeSetupBlocks original183 = normalizeSetupBlocks target183 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source183_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target183_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨183, by decide +kernel⟩).1

theorem chunkLength183 : (original183.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source183_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨183, by decide +kernel⟩).2

theorem chunkChecked184 : normalizeSetupBlocks original184 = normalizeSetupBlocks target184 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source184_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target184_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨184, by decide +kernel⟩).1

theorem chunkLength184 : (original184.map Setup.Block.length).sum = 1206 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source184_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨184, by decide +kernel⟩).2

theorem chunkChecked185 : normalizeSetupBlocks original185 = normalizeSetupBlocks target185 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source185_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target185_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨185, by decide +kernel⟩).1

theorem chunkLength185 : (original185.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source185_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨185, by decide +kernel⟩).2

theorem chunkChecked186 : normalizeSetupBlocks original186 = normalizeSetupBlocks target186 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source186_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target186_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨186, by decide +kernel⟩).1

theorem chunkLength186 : (original186.map Setup.Block.length).sum = 1226 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source186_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨186, by decide +kernel⟩).2

theorem chunkChecked187 : normalizeSetupBlocks original187 = normalizeSetupBlocks target187 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source187_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target187_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨187, by decide +kernel⟩).1

theorem chunkLength187 : (original187.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source187_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨187, by decide +kernel⟩).2

theorem chunkChecked188 : normalizeSetupBlocks original188 = normalizeSetupBlocks target188 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source188_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target188_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨188, by decide +kernel⟩).1

theorem chunkLength188 : (original188.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source188_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨188, by decide +kernel⟩).2

theorem chunkChecked189 : normalizeSetupBlocks original189 = normalizeSetupBlocks target189 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source189_binding, Airbender.Compiler.ShiftPrefixChecks.Column6.target189_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨189, by decide +kernel⟩).1

theorem chunkLength189 : (original189.map Setup.Block.length).sum = 908 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.source189_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨189, by decide +kernel⟩).2

theorem checkedRegion0Part0Length : (target0Region0.map Setup.Block.length).sum = 1 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region0_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨190, by decide +kernel⟩).2

theorem checkedRegion1Part0Length : (target0Region1.map Setup.Block.length).sum = 256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region1_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨191, by decide +kernel⟩).2

theorem checkedRegion2Part0Length : (target0Region2.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region2_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨192, by decide +kernel⟩).2

theorem checkedRegion3Part0Length : (target0Region3.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region3_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨193, by decide +kernel⟩).2

theorem checkedRegion4Part0Length : (target0Region4.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region4_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨194, by decide +kernel⟩).2

theorem checkedRegion5Part0Length : (target0Region5.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region5_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨195, by decide +kernel⟩).2

theorem checkedRegion6Part0Length : (target0Region6.map Setup.Block.length).sum = 2162 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target0Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨196, by decide +kernel⟩).2

theorem checkedRegion6Part1Length : (target1Region6.map Setup.Block.length).sum = 1568 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target1Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨197, by decide +kernel⟩).2

theorem checkedRegion6Part2Length : (target2Region6.map Setup.Block.length).sum = 1528 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target2Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨198, by decide +kernel⟩).2

theorem checkedRegion6Part3Length : (target3Region6.map Setup.Block.length).sum = 1520 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target3Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨199, by decide +kernel⟩).2

theorem checkedRegion6Part4Length : (target4Region6.map Setup.Block.length).sum = 1344 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target4Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨200, by decide +kernel⟩).2

theorem checkedRegion6Part5Length : (target5Region6.map Setup.Block.length).sum = 1488 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target5Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨201, by decide +kernel⟩).2

theorem checkedRegion6Part6Length : (target6Region6.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target6Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨202, by decide +kernel⟩).2

theorem checkedRegion6Part7Length : (target7Region6.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target7Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨203, by decide +kernel⟩).2

theorem checkedRegion6Part8Length : (target8Region6.map Setup.Block.length).sum = 1480 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target8Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨204, by decide +kernel⟩).2

theorem checkedRegion6Part9Length : (target9Region6.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target9Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨205, by decide +kernel⟩).2

theorem checkedRegion6Part10Length : (target10Region6.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target10Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨206, by decide +kernel⟩).2

theorem checkedRegion6Part11Length : (target11Region6.map Setup.Block.length).sum = 1448 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target11Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨207, by decide +kernel⟩).2

theorem checkedRegion6Part12Length : (target12Region6.map Setup.Block.length).sum = 1120 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target12Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨208, by decide +kernel⟩).2

theorem checkedRegion6Part13Length : (target13Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target13Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨209, by decide +kernel⟩).2

theorem checkedRegion6Part14Length : (target14Region6.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target14Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨210, by decide +kernel⟩).2

theorem checkedRegion6Part15Length : (target15Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target15Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨211, by decide +kernel⟩).2

theorem checkedRegion6Part16Length : (target16Region6.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target16Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨212, by decide +kernel⟩).2

theorem checkedRegion6Part17Length : (target17Region6.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target17Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨213, by decide +kernel⟩).2

theorem checkedRegion6Part18Length : (target18Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target18Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨214, by decide +kernel⟩).2

theorem checkedRegion6Part19Length : (target19Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target19Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨215, by decide +kernel⟩).2

theorem checkedRegion6Part20Length : (target20Region6.map Setup.Block.length).sum = 1288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target20Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨216, by decide +kernel⟩).2

theorem checkedRegion6Part21Length : (target21Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target21Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨217, by decide +kernel⟩).2

theorem checkedRegion6Part22Length : (target22Region6.map Setup.Block.length).sum = 1272 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target22Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨218, by decide +kernel⟩).2

theorem checkedRegion6Part23Length : (target23Region6.map Setup.Block.length).sum = 1112 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target23Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨219, by decide +kernel⟩).2

theorem checkedRegion6Part24Length : (target24Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target24Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨220, by decide +kernel⟩).2

theorem checkedRegion6Part25Length : (target25Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target25Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨221, by decide +kernel⟩).2

theorem checkedRegion6Part26Length : (target26Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target26Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨222, by decide +kernel⟩).2

theorem checkedRegion6Part27Length : (target27Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target27Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨223, by decide +kernel⟩).2

theorem checkedRegion6Part28Length : (target28Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target28Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨224, by decide +kernel⟩).2

theorem checkedRegion6Part29Length : (target29Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target29Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨225, by decide +kernel⟩).2

theorem checkedRegion6Part30Length : (target30Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target30Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨226, by decide +kernel⟩).2

theorem checkedRegion6Part31Length : (target31Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target31Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨227, by decide +kernel⟩).2

theorem checkedRegion6Part32Length : (target32Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target32Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨228, by decide +kernel⟩).2

theorem checkedRegion6Part33Length : (target33Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target33Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨229, by decide +kernel⟩).2

theorem checkedRegion6Part34Length : (target34Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target34Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨230, by decide +kernel⟩).2

theorem checkedRegion6Part35Length : (target35Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target35Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨231, by decide +kernel⟩).2

theorem checkedRegion6Part36Length : (target36Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target36Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨232, by decide +kernel⟩).2

theorem checkedRegion6Part37Length : (target37Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target37Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨233, by decide +kernel⟩).2

theorem checkedRegion6Part38Length : (target38Region6.map Setup.Block.length).sum = 1248 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target38Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨234, by decide +kernel⟩).2

theorem checkedRegion6Part39Length : (target39Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target39Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨235, by decide +kernel⟩).2

theorem checkedRegion6Part40Length : (target40Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target40Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨236, by decide +kernel⟩).2

theorem checkedRegion6Part41Length : (target41Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target41Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨237, by decide +kernel⟩).2

theorem checkedRegion6Part42Length : (target42Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target42Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨238, by decide +kernel⟩).2

theorem checkedRegion6Part43Length : (target43Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target43Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨239, by decide +kernel⟩).2

theorem checkedRegion6Part44Length : (target44Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target44Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨240, by decide +kernel⟩).2

theorem checkedRegion6Part45Length : (target45Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target45Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨241, by decide +kernel⟩).2

theorem checkedRegion6Part46Length : (target46Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target46Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨242, by decide +kernel⟩).2

theorem checkedRegion6Part47Length : (target47Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target47Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨243, by decide +kernel⟩).2

theorem checkedRegion6Part48Length : (target48Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target48Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨244, by decide +kernel⟩).2

theorem checkedRegion6Part49Length : (target49Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target49Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨245, by decide +kernel⟩).2

theorem checkedRegion6Part50Length : (target50Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target50Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨246, by decide +kernel⟩).2

theorem checkedRegion6Part51Length : (target51Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target51Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨247, by decide +kernel⟩).2

theorem checkedRegion6Part52Length : (target52Region6.map Setup.Block.length).sum = 1944 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target52Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨248, by decide +kernel⟩).2

theorem checkedRegion6Part53Length : (target53Region6.map Setup.Block.length).sum = 1520 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target53Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨249, by decide +kernel⟩).2

theorem checkedRegion6Part54Length : (target54Region6.map Setup.Block.length).sum = 1328 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target54Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨250, by decide +kernel⟩).2

theorem checkedRegion6Part55Length : (target55Region6.map Setup.Block.length).sum = 1304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target55Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨251, by decide +kernel⟩).2

theorem checkedRegion6Part56Length : (target56Region6.map Setup.Block.length).sum = 1472 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target56Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨252, by decide +kernel⟩).2

theorem checkedRegion6Part57Length : (target57Region6.map Setup.Block.length).sum = 1296 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target57Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨253, by decide +kernel⟩).2

theorem checkedRegion6Part58Length : (target58Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target58Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨254, by decide +kernel⟩).2

theorem checkedRegion6Part59Length : (target59Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target59Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨255, by decide +kernel⟩).2

theorem checkedRegion6Part60Length : (target60Region6.map Setup.Block.length).sum = 1288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target60Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨256, by decide +kernel⟩).2

theorem checkedRegion6Part61Length : (target61Region6.map Setup.Block.length).sum = 1244 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target61Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨257, by decide +kernel⟩).2

theorem checkedRegion6Part62Length : (target62Region6.map Setup.Block.length).sum = 1132 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target62Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨258, by decide +kernel⟩).2

theorem checkedRegion6Part63Length : (target63Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target63Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨259, by decide +kernel⟩).2

theorem checkedRegion6Part64Length : (target64Region6.map Setup.Block.length).sum = 1248 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target64Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨260, by decide +kernel⟩).2

theorem checkedRegion6Part65Length : (target65Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target65Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨261, by decide +kernel⟩).2

theorem checkedRegion6Part66Length : (target66Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target66Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨262, by decide +kernel⟩).2

theorem checkedRegion6Part67Length : (target67Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target67Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨263, by decide +kernel⟩).2

theorem checkedRegion6Part68Length : (target68Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target68Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨264, by decide +kernel⟩).2

theorem checkedRegion6Part69Length : (target69Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target69Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨265, by decide +kernel⟩).2

theorem checkedRegion6Part70Length : (target70Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target70Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨266, by decide +kernel⟩).2

theorem checkedRegion6Part71Length : (target71Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target71Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨267, by decide +kernel⟩).2

theorem checkedRegion6Part72Length : (target72Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target72Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨268, by decide +kernel⟩).2

theorem checkedRegion6Part73Length : (target73Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target73Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨269, by decide +kernel⟩).2

theorem checkedRegion6Part74Length : (target74Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target74Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨270, by decide +kernel⟩).2

theorem checkedRegion6Part75Length : (target75Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target75Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨271, by decide +kernel⟩).2

theorem checkedRegion6Part76Length : (target76Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target76Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨272, by decide +kernel⟩).2

theorem checkedRegion6Part77Length : (target77Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target77Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨273, by decide +kernel⟩).2

theorem checkedRegion6Part78Length : (target78Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target78Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨274, by decide +kernel⟩).2

theorem checkedRegion6Part79Length : (target79Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target79Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨275, by decide +kernel⟩).2

theorem checkedRegion6Part80Length : (target80Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target80Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨276, by decide +kernel⟩).2

theorem checkedRegion6Part81Length : (target81Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target81Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨277, by decide +kernel⟩).2

theorem checkedRegion6Part82Length : (target82Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target82Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨278, by decide +kernel⟩).2

theorem checkedRegion6Part83Length : (target83Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target83Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨279, by decide +kernel⟩).2

theorem checkedRegion6Part84Length : (target84Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target84Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨280, by decide +kernel⟩).2

theorem checkedRegion6Part85Length : (target85Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target85Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨281, by decide +kernel⟩).2

theorem checkedRegion6Part86Length : (target86Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target86Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨282, by decide +kernel⟩).2

theorem checkedRegion6Part87Length : (target87Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target87Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨283, by decide +kernel⟩).2

theorem checkedRegion6Part88Length : (target88Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target88Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨284, by decide +kernel⟩).2

theorem checkedRegion6Part89Length : (target89Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target89Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨285, by decide +kernel⟩).2

theorem checkedRegion6Part90Length : (target90Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target90Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨286, by decide +kernel⟩).2

theorem checkedRegion6Part91Length : (target91Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target91Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨287, by decide +kernel⟩).2

theorem checkedRegion6Part92Length : (target92Region6.map Setup.Block.length).sum = 1248 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target92Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨288, by decide +kernel⟩).2

theorem checkedRegion6Part93Length : (target93Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target93Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨289, by decide +kernel⟩).2

theorem checkedRegion6Part94Length : (target94Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target94Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨290, by decide +kernel⟩).2

theorem checkedRegion6Part95Length : (target95Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target95Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨291, by decide +kernel⟩).2

theorem checkedRegion6Part96Length : (target96Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target96Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨292, by decide +kernel⟩).2

theorem checkedRegion6Part97Length : (target97Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target97Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨293, by decide +kernel⟩).2

theorem checkedRegion6Part98Length : (target98Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target98Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨294, by decide +kernel⟩).2

theorem checkedRegion6Part99Length : (target99Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target99Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨295, by decide +kernel⟩).2

theorem checkedRegion6Part100Length : (target100Region6.map Setup.Block.length).sum = 1240 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target100Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨296, by decide +kernel⟩).2

theorem checkedRegion6Part101Length : (target101Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target101Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨297, by decide +kernel⟩).2

theorem checkedRegion6Part102Length : (target102Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target102Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨298, by decide +kernel⟩).2

theorem checkedRegion6Part103Length : (target103Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target103Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨299, by decide +kernel⟩).2

theorem checkedRegion6Part104Length : (target104Region6.map Setup.Block.length).sum = 1232 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target104Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨300, by decide +kernel⟩).2

theorem checkedRegion6Part105Length : (target105Region6.map Setup.Block.length).sum = 1080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target105Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨301, by decide +kernel⟩).2

theorem checkedRegion6Part106Length : (target106Region6.map Setup.Block.length).sum = 2490 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target106Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨302, by decide +kernel⟩).2

theorem checkedRegion6Part107Length : (target107Region6.map Setup.Block.length).sum = 2296 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target107Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨303, by decide +kernel⟩).2

theorem checkedRegion6Part108Length : (target108Region6.map Setup.Block.length).sum = 2304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target108Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨304, by decide +kernel⟩).2

theorem checkedRegion6Part109Length : (target109Region6.map Setup.Block.length).sum = 2094 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target109Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨305, by decide +kernel⟩).2

theorem checkedRegion6Part110Length : (target110Region6.map Setup.Block.length).sum = 2290 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target110Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨306, by decide +kernel⟩).2

theorem checkedRegion6Part111Length : (target111Region6.map Setup.Block.length).sum = 2304 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target111Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨307, by decide +kernel⟩).2

theorem checkedRegion6Part112Length : (target112Region6.map Setup.Block.length).sum = 2288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target112Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨308, by decide +kernel⟩).2

theorem checkedRegion6Part113Length : (target113Region6.map Setup.Block.length).sum = 2080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target113Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨309, by decide +kernel⟩).2

theorem checkedRegion6Part114Length : (target114Region6.map Setup.Block.length).sum = 2280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target114Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨310, by decide +kernel⟩).2

theorem checkedRegion6Part115Length : (target115Region6.map Setup.Block.length).sum = 2078 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target115Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨311, by decide +kernel⟩).2

theorem checkedRegion6Part116Length : (target116Region6.map Setup.Block.length).sum = 2274 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target116Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨312, by decide +kernel⟩).2

theorem checkedRegion6Part117Length : (target117Region6.map Setup.Block.length).sum = 2280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target117Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨313, by decide +kernel⟩).2

theorem checkedRegion6Part118Length : (target118Region6.map Setup.Block.length).sum = 2080 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target118Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨314, by decide +kernel⟩).2

theorem checkedRegion6Part119Length : (target119Region6.map Setup.Block.length).sum = 2272 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target119Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨315, by decide +kernel⟩).2

theorem checkedRegion6Part120Length : (target120Region6.map Setup.Block.length).sum = 2072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target120Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨316, by decide +kernel⟩).2

theorem checkedRegion6Part121Length : (target121Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target121Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨317, by decide +kernel⟩).2

theorem checkedRegion6Part122Length : (target122Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target122Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨318, by decide +kernel⟩).2

theorem checkedRegion6Part123Length : (target123Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target123Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨319, by decide +kernel⟩).2

theorem checkedRegion6Part124Length : (target124Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target124Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨320, by decide +kernel⟩).2

theorem checkedRegion6Part125Length : (target125Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target125Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨321, by decide +kernel⟩).2

theorem checkedRegion6Part126Length : (target126Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target126Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨322, by decide +kernel⟩).2

theorem checkedRegion6Part127Length : (target127Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target127Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨323, by decide +kernel⟩).2

theorem checkedRegion6Part128Length : (target128Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target128Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨324, by decide +kernel⟩).2

theorem checkedRegion6Part129Length : (target129Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target129Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨325, by decide +kernel⟩).2

theorem checkedRegion6Part130Length : (target130Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target130Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨326, by decide +kernel⟩).2

theorem checkedRegion6Part131Length : (target131Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target131Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨327, by decide +kernel⟩).2

theorem checkedRegion6Part132Length : (target132Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target132Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨328, by decide +kernel⟩).2

theorem checkedRegion6Part133Length : (target133Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target133Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨329, by decide +kernel⟩).2

theorem checkedRegion6Part134Length : (target134Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target134Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨330, by decide +kernel⟩).2

theorem checkedRegion6Part135Length : (target135Region6.map Setup.Block.length).sum = 2048 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target135Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨331, by decide +kernel⟩).2

theorem checkedRegion6Part136Length : (target136Region6.map Setup.Block.length).sum = 2312 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target136Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨332, by decide +kernel⟩).2

theorem checkedRegion6Part137Length : (target137Region6.map Setup.Block.length).sum = 1792 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target137Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨333, by decide +kernel⟩).2

theorem checkedRegion6Part138Length : (target138Region6.map Setup.Block.length).sum = 1576 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target138Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨334, by decide +kernel⟩).2

theorem checkedRegion6Part139Length : (target139Region6.map Setup.Block.length).sum = 1504 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target139Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨335, by decide +kernel⟩).2

theorem checkedRegion6Part140Length : (target140Region6.map Setup.Block.length).sum = 1520 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target140Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨336, by decide +kernel⟩).2

theorem checkedRegion6Part141Length : (target141Region6.map Setup.Block.length).sum = 1352 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target141Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨337, by decide +kernel⟩).2

theorem checkedRegion6Part142Length : (target142Region6.map Setup.Block.length).sum = 1456 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target142Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨338, by decide +kernel⟩).2

theorem checkedRegion6Part143Length : (target143Region6.map Setup.Block.length).sum = 1320 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target143Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨339, by decide +kernel⟩).2

theorem checkedRegion6Part144Length : (target144Region6.map Setup.Block.length).sum = 1312 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target144Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨340, by decide +kernel⟩).2

theorem checkedRegion6Part145Length : (target145Region6.map Setup.Block.length).sum = 1456 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target145Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨341, by decide +kernel⟩).2

theorem checkedRegion6Part146Length : (target146Region6.map Setup.Block.length).sum = 1320 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target146Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨342, by decide +kernel⟩).2

theorem checkedRegion6Part147Length : (target147Region6.map Setup.Block.length).sum = 1320 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target147Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨343, by decide +kernel⟩).2

theorem checkedRegion6Part148Length : (target148Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target148Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨344, by decide +kernel⟩).2

theorem checkedRegion6Part149Length : (target149Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target149Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨345, by decide +kernel⟩).2

theorem checkedRegion6Part150Length : (target150Region6.map Setup.Block.length).sum = 1288 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target150Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨346, by decide +kernel⟩).2

theorem checkedRegion6Part151Length : (target151Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target151Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨347, by decide +kernel⟩).2

theorem checkedRegion6Part152Length : (target152Region6.map Setup.Block.length).sum = 1272 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target152Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨348, by decide +kernel⟩).2

theorem checkedRegion6Part153Length : (target153Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target153Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨349, by decide +kernel⟩).2

theorem checkedRegion6Part154Length : (target154Region6.map Setup.Block.length).sum = 1296 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target154Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨350, by decide +kernel⟩).2

theorem checkedRegion6Part155Length : (target155Region6.map Setup.Block.length).sum = 1264 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target155Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨351, by decide +kernel⟩).2

theorem checkedRegion6Part156Length : (target156Region6.map Setup.Block.length).sum = 1112 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target156Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨352, by decide +kernel⟩).2

theorem checkedRegion6Part157Length : (target157Region6.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target157Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨353, by decide +kernel⟩).2

theorem checkedRegion6Part158Length : (target158Region6.map Setup.Block.length).sum = 1256 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target158Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨354, by decide +kernel⟩).2

theorem checkedRegion6Part159Length : (target159Region6.map Setup.Block.length).sum = 1280 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target159Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨355, by decide +kernel⟩).2

theorem checkedRegion6Part160Length : (target160Region6.map Setup.Block.length).sum = 1286 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target160Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨356, by decide +kernel⟩).2

theorem checkedRegion6Part161Length : (target161Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target161Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨357, by decide +kernel⟩).2

theorem checkedRegion6Part162Length : (target162Region6.map Setup.Block.length).sum = 1210 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target162Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨358, by decide +kernel⟩).2

theorem checkedRegion6Part163Length : (target163Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target163Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨359, by decide +kernel⟩).2

theorem checkedRegion6Part164Length : (target164Region6.map Setup.Block.length).sum = 1214 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target164Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨360, by decide +kernel⟩).2

theorem checkedRegion6Part165Length : (target165Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target165Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨361, by decide +kernel⟩).2

theorem checkedRegion6Part166Length : (target166Region6.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target166Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨362, by decide +kernel⟩).2

theorem checkedRegion6Part167Length : (target167Region6.map Setup.Block.length).sum = 1234 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target167Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨363, by decide +kernel⟩).2

theorem checkedRegion6Part168Length : (target168Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target168Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨364, by decide +kernel⟩).2

theorem checkedRegion6Part169Length : (target169Region6.map Setup.Block.length).sum = 1206 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target169Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨365, by decide +kernel⟩).2

theorem checkedRegion6Part170Length : (target170Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target170Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨366, by decide +kernel⟩).2

theorem checkedRegion6Part171Length : (target171Region6.map Setup.Block.length).sum = 1209 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target171Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨367, by decide +kernel⟩).2

theorem checkedRegion6Part172Length : (target172Region6.map Setup.Block.length).sum = 1073 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target172Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨368, by decide +kernel⟩).2

theorem checkedRegion6Part173Length : (target173Region6.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target173Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨369, by decide +kernel⟩).2

theorem checkedRegion6Part174Length : (target174Region6.map Setup.Block.length).sum = 1198 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target174Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨370, by decide +kernel⟩).2

theorem checkedRegion6Part175Length : (target175Region6.map Setup.Block.length).sum = 1096 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target175Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨371, by decide +kernel⟩).2

theorem checkedRegion6Part176Length : (target176Region6.map Setup.Block.length).sum = 1193 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target176Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨372, by decide +kernel⟩).2

theorem checkedRegion6Part177Length : (target177Region6.map Setup.Block.length).sum = 1089 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target177Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨373, by decide +kernel⟩).2

theorem checkedRegion6Part178Length : (target178Region6.map Setup.Block.length).sum = 1079 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target178Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨374, by decide +kernel⟩).2

theorem checkedRegion6Part179Length : (target179Region6.map Setup.Block.length).sum = 1199 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target179Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨375, by decide +kernel⟩).2

theorem checkedRegion6Part180Length : (target180Region6.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target180Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨376, by decide +kernel⟩).2

theorem checkedRegion6Part181Length : (target181Region6.map Setup.Block.length).sum = 1193 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target181Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨377, by decide +kernel⟩).2

theorem checkedRegion6Part182Length : (target182Region6.map Setup.Block.length).sum = 1097 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target182Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨378, by decide +kernel⟩).2

theorem checkedRegion6Part183Length : (target183Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target183Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨379, by decide +kernel⟩).2

theorem checkedRegion6Part184Length : (target184Region6.map Setup.Block.length).sum = 1206 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target184Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨380, by decide +kernel⟩).2

theorem checkedRegion6Part185Length : (target185Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target185Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨381, by decide +kernel⟩).2

theorem checkedRegion6Part186Length : (target186Region6.map Setup.Block.length).sum = 1226 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target186Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨382, by decide +kernel⟩).2

theorem checkedRegion6Part187Length : (target187Region6.map Setup.Block.length).sum = 1072 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target187Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨383, by decide +kernel⟩).2

theorem checkedRegion6Part188Length : (target188Region6.map Setup.Block.length).sum = 1064 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target188Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨384, by decide +kernel⟩).2

theorem checkedRegion6Part189Length : (target189Region6.map Setup.Block.length).sum = 908 := by
  rw [Airbender.Compiler.ShiftPrefixChecks.Column6.target189Region6_binding]
  exact (Airbender.Compiler.ShiftPrefixChecks.Column6.facts ⟨385, by decide +kernel⟩).2

end Airbender.Compiler.ShiftPrefixNative.Column6
