import Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column2.Part0
import Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column2.Part1
import Airbender.Import.PackedSetupEmbed
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.PackedSetupNormalization

namespace Airbender.Compiler.SubwordFixedChecks.Column2
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupNormalization
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

-- Each request stays inside the five fixed regions.
import_setup_code_capture from "artifacts/setup/subword-memory.json" [
  source0 := column 2 block_start 0 block_count 1 unpacked,
  target0Region0 := region 0 column 2 block_start 0 block_count 1 packed_bytes 0,
  target0Region1 := region 29 column 2 block_start 0 block_count 1 packed_bytes 0,
  target0Region2 := region 30 column 2 block_start 0 block_count 1 packed_bytes 0,
  target0Region3 := region 42 column 2 block_start 0 block_count 1 packed_bytes 0,
  source1 := column 2 block_start 1 block_count 1 unpacked,
  target1Region3 := region 42 column 2 block_start 1 block_count 1 packed_bytes 0,
  source2 := column 2 block_start 2 block_count 1 unpacked,
  target2Region4 := region 43 column 2 block_start 0 block_count 1 packed_bytes 0,
  source3 := column 2 block_start 3 block_count 1 unpacked,
  target3Region4 := region 43 column 2 block_start 1 block_count 1 packed_bytes 0,
  source4 := column 2 block_start 4 block_count 1 unpacked,
  target4Region4 := region 43 column 2 block_start 2 block_count 1 packed_bytes 0,
  source5 := column 2 block_start 5 block_count 1 unpacked,
  target5Region4 := region 43 column 2 block_start 3 block_count 1 packed_bytes 0]

def targets0 : List BlockCode := target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3
numeric_data_binding source0_binding : Airbender.Compiler.SubwordPrefixNative.Column2.original0 = source0.map BlockCode.decode
numeric_data_binding target0_binding : Airbender.Compiler.SubwordPrefixNative.Column2.target0 = targets0.map BlockCode.decode

def targets1 : List BlockCode := target1Region3
numeric_data_binding source1_binding : Airbender.Compiler.SubwordPrefixNative.Column2.original1 = source1.map BlockCode.decode
numeric_data_binding target1_binding : Airbender.Compiler.SubwordPrefixNative.Column2.target1 = targets1.map BlockCode.decode

def targets2 : List BlockCode := target2Region4
numeric_data_binding source2_binding : Airbender.Compiler.SubwordPrefixNative.Column2.original2 = source2.map BlockCode.decode
numeric_data_binding target2_binding : Airbender.Compiler.SubwordPrefixNative.Column2.target2 = targets2.map BlockCode.decode

def targets3 : List BlockCode := target3Region4
numeric_data_binding source3_binding : Airbender.Compiler.SubwordPrefixNative.Column2.original3 = source3.map BlockCode.decode
numeric_data_binding target3_binding : Airbender.Compiler.SubwordPrefixNative.Column2.target3 = targets3.map BlockCode.decode

def targets4 : List BlockCode := target4Region4
numeric_data_binding source4_binding : Airbender.Compiler.SubwordPrefixNative.Column2.original4 = source4.map BlockCode.decode
numeric_data_binding target4_binding : Airbender.Compiler.SubwordPrefixNative.Column2.target4 = targets4.map BlockCode.decode

def targets5 : List BlockCode := target5Region4
numeric_data_binding source5_binding : Airbender.Compiler.SubwordPrefixNative.Column2.original5 = source5.map BlockCode.decode
numeric_data_binding target5_binding : Airbender.Compiler.SubwordPrefixNative.Column2.target5 = targets5.map BlockCode.decode

def requests : List Request := [
  ⟨source0, targets0, 360449⟩,
  ⟨source1, targets1, 32768⟩,
  ⟨source2, targets2, 65664⟩,
  ⟨source3, targets3, 65536⟩,
  ⟨source4, targets4, 98176⟩,
  ⟨source5, targets5, 32768⟩]

theorem checked : PackedSetupNormalization.check requests = true := by decide +kernel

theorem facts (index : Fin requests.length) : Fact (requests.get index) :=
  PackedSetupNormalization.check_sound_at requests checked index

end Airbender.Compiler.SubwordFixedChecks.Column2

namespace Airbender.Compiler.SubwordPrefixNative.Column2
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem chunkChecked0 : normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source0_binding, Airbender.Compiler.SubwordFixedChecks.Column2.target0_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨0, by decide +kernel⟩).1

theorem chunkLength0 : (original0.map Setup.Block.length).sum = 360449 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source0_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨0, by decide +kernel⟩).2

theorem chunkChecked1 : normalizeSetupBlocks original1 = normalizeSetupBlocks target1 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source1_binding, Airbender.Compiler.SubwordFixedChecks.Column2.target1_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨1, by decide +kernel⟩).1

theorem chunkLength1 : (original1.map Setup.Block.length).sum = 32768 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source1_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨1, by decide +kernel⟩).2

theorem chunkChecked2 : normalizeSetupBlocks original2 = normalizeSetupBlocks target2 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source2_binding, Airbender.Compiler.SubwordFixedChecks.Column2.target2_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨2, by decide +kernel⟩).1

theorem chunkLength2 : (original2.map Setup.Block.length).sum = 65664 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source2_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨2, by decide +kernel⟩).2

theorem chunkChecked3 : normalizeSetupBlocks original3 = normalizeSetupBlocks target3 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source3_binding, Airbender.Compiler.SubwordFixedChecks.Column2.target3_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨3, by decide +kernel⟩).1

theorem chunkLength3 : (original3.map Setup.Block.length).sum = 65536 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source3_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨3, by decide +kernel⟩).2

theorem chunkChecked4 : normalizeSetupBlocks original4 = normalizeSetupBlocks target4 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source4_binding, Airbender.Compiler.SubwordFixedChecks.Column2.target4_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨4, by decide +kernel⟩).1

theorem chunkLength4 : (original4.map Setup.Block.length).sum = 98176 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source4_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨4, by decide +kernel⟩).2

theorem chunkChecked5 : normalizeSetupBlocks original5 = normalizeSetupBlocks target5 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source5_binding, Airbender.Compiler.SubwordFixedChecks.Column2.target5_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨5, by decide +kernel⟩).1

theorem chunkLength5 : (original5.map Setup.Block.length).sum = 32768 := by
  rw [Airbender.Compiler.SubwordFixedChecks.Column2.source5_binding]
  exact (Airbender.Compiler.SubwordFixedChecks.Column2.facts ⟨5, by decide +kernel⟩).2

end Airbender.Compiler.SubwordPrefixNative.Column2
