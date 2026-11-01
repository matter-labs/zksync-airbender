import Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column1.Part0
import Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column1.Part1
import Airbender.Import.PackedSetupEmbed
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.PackedSetupNormalization

namespace Airbender.Compiler.SubwordFixedChecks.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupNormalization
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

-- Each request stays inside the five fixed regions.
import_setup_code_capture from "artifacts/setup/subword-memory.json" [
  source0 := column 1 block_start 0 block_count 1 unpacked,
  target0Region0 := region 0 column 1 block_start 0 block_count 1 packed_bytes 0,
  source1 := column 1 block_start 1 block_count 1 unpacked,
  target1Region1 := region 29 column 1 block_start 0 block_count 1 packed_bytes 0,
  source2 := column 1 block_start 2 block_count 1 unpacked,
  target2Region1 := region 29 column 1 block_start 1 block_count 1 packed_bytes 0,
  source3 := column 1 block_start 3 block_count 1 unpacked,
  target3Region2 := region 30 column 1 block_start 0 block_count 1 packed_bytes 0,
  source4 := column 1 block_start 4 block_count 1 unpacked,
  target4Region2 := region 30 column 1 block_start 1 block_count 1 packed_bytes 0,
  target4Region3 := region 42 column 1 block_start 0 block_count 1 packed_bytes 0,
  source5 := column 1 block_start 5 block_count 1 unpacked,
  target5Region3 := region 42 column 1 block_start 1 block_count 1 packed_bytes 0,
  source6 := column 1 block_start 6 block_count 1 unpacked,
  target6Region3 := region 42 column 1 block_start 2 block_count 1 packed_bytes 0,
  source7 := column 1 block_start 7 block_count 1 unpacked,
  target7Region4 := region 43 column 1 block_start 0 block_count 1 packed_bytes 0,
  source8 := column 1 block_start 8 block_count 1 unpacked,
  target8Region4 := region 43 column 1 block_start 1 block_count 1 packed_bytes 0,
  source9 := column 1 block_start 9 block_count 1 unpacked,
  target9Region4 := region 43 column 1 block_start 2 block_count 1 packed_bytes 0,
  source10 := column 1 block_start 10 block_count 1 unpacked,
  target10Region4 := region 43 column 1 block_start 3 block_count 1 packed_bytes 0,
  source11 := column 1 block_start 11 block_count 1 unpacked,
  target11Region4 := region 43 column 1 block_start 4 block_count 1 packed_bytes 0]

def targets0 : List BlockCode := target0Region0
numeric_data_binding source0_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original0 = source0.map BlockCode.decode
numeric_data_binding target0_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target0 = targets0.map BlockCode.decode

def targets1 : List BlockCode := target1Region1
numeric_data_binding source1_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original1 = source1.map BlockCode.decode
numeric_data_binding target1_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target1 = targets1.map BlockCode.decode

def targets2 : List BlockCode := target2Region1
numeric_data_binding source2_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original2 = source2.map BlockCode.decode
numeric_data_binding target2_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target2 = targets2.map BlockCode.decode

def targets3 : List BlockCode := target3Region2
numeric_data_binding source3_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original3 = source3.map BlockCode.decode
numeric_data_binding target3_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target3 = targets3.map BlockCode.decode

def targets4 : List BlockCode := target4Region2 ++ target4Region3
numeric_data_binding source4_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original4 = source4.map BlockCode.decode
numeric_data_binding target4_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target4 = targets4.map BlockCode.decode

def targets5 : List BlockCode := target5Region3
numeric_data_binding source5_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original5 = source5.map BlockCode.decode
numeric_data_binding target5_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target5 = targets5.map BlockCode.decode

def targets6 : List BlockCode := target6Region3
numeric_data_binding source6_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original6 = source6.map BlockCode.decode
numeric_data_binding target6_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target6 = targets6.map BlockCode.decode

def targets7 : List BlockCode := target7Region4
numeric_data_binding source7_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original7 = source7.map BlockCode.decode
numeric_data_binding target7_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target7 = targets7.map BlockCode.decode

def targets8 : List BlockCode := target8Region4
numeric_data_binding source8_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original8 = source8.map BlockCode.decode
numeric_data_binding target8_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target8 = targets8.map BlockCode.decode

def targets9 : List BlockCode := target9Region4
numeric_data_binding source9_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original9 = source9.map BlockCode.decode
numeric_data_binding target9_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target9 = targets9.map BlockCode.decode

def targets10 : List BlockCode := target10Region4
numeric_data_binding source10_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original10 = source10.map BlockCode.decode
numeric_data_binding target10_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target10 = targets10.map BlockCode.decode

def targets11 : List BlockCode := target11Region4
numeric_data_binding source11_binding : Airbender.Compiler.SubwordPrefixNative.Column1.original11 = source11.map BlockCode.decode
numeric_data_binding target11_binding : Airbender.Compiler.SubwordPrefixNative.Column1.target11 = targets11.map BlockCode.decode

def requests : List Request := [
  ⟨source0, targets0, 1⟩,
  ⟨source1, targets1, 65536⟩,
  ⟨source2, targets2, 65536⟩,
  ⟨source3, targets3, 65536⟩,
  ⟨source4, targets4, 65792⟩,
  ⟨source5, targets5, 65280⟩,
  ⟨source6, targets6, 65536⟩,
  ⟨source7, targets7, 65536⟩,
  ⟨source8, targets8, 65536⟩,
  ⟨source9, targets9, 65536⟩,
  ⟨source10, targets10, 32768⟩,
  ⟨source11, targets11, 32768⟩]

theorem checked : PackedSetupNormalization.check requests = true := by decide +kernel

theorem facts (index : Fin requests.length) : Fact (requests.get index) :=
  PackedSetupNormalization.check_sound_at requests checked index

end Airbender.Compiler.SubwordFixedChecks.Column1

namespace Airbender.Compiler.SubwordPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source0_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target0_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨0, by decide +kernel⟩).1

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 1 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source0_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨0, by decide +kernel⟩).2

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source1_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target1_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨1, by decide +kernel⟩).1

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source1_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨1, by decide +kernel⟩).2

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source2_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target2_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨2, by decide +kernel⟩).1

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source2_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨2, by decide +kernel⟩).2

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source3_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target3_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨3, by decide +kernel⟩).1

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source3_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨3, by decide +kernel⟩).2

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source4_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target4_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨4, by decide +kernel⟩).1

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 65792 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source4_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨4, by decide +kernel⟩).2

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source5_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target5_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨5, by decide +kernel⟩).1

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 65280 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source5_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨5, by decide +kernel⟩).2

theorem chunkChecked6 : normalizeSetupBlocks original6 = normalizeSetupBlocks target6 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source6_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target6_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨6, by decide +kernel⟩).1

theorem chunkLength6 : (original6.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source6_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨6, by decide +kernel⟩).2

theorem chunkChecked7 : normalizeSetupBlocks original7 = normalizeSetupBlocks target7 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source7_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target7_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨7, by decide +kernel⟩).1

theorem chunkLength7 : (original7.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source7_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨7, by decide +kernel⟩).2

theorem chunkChecked8 : normalizeSetupBlocks original8 = normalizeSetupBlocks target8 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source8_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target8_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨8, by decide +kernel⟩).1

theorem chunkLength8 : (original8.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source8_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨8, by decide +kernel⟩).2

theorem chunkChecked9 : normalizeSetupBlocks original9 = normalizeSetupBlocks target9 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source9_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target9_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨9, by decide +kernel⟩).1

theorem chunkLength9 : (original9.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source9_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨9, by decide +kernel⟩).2

theorem chunkChecked10 : normalizeSetupBlocks original10 = normalizeSetupBlocks target10 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source10_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target10_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨10, by decide +kernel⟩).1

theorem chunkLength10 : (original10.map Setup.Block.length).sum = 32768 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source10_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨10, by decide +kernel⟩).2

theorem chunkChecked11 : normalizeSetupBlocks original11 = normalizeSetupBlocks target11 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source11_binding, Airbender.Compiler.SubwordFixedChecks.Column1.target11_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨11, by decide +kernel⟩).1

theorem chunkLength11 : (original11.map Setup.Block.length).sum = 32768 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column1.source11_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column1.facts ⟨11, by decide +kernel⟩).2

end Airbender.Compiler.SubwordPrefixNative.Column1
