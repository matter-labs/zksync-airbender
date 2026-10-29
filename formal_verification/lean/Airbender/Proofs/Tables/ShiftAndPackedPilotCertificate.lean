import Airbender.Data.Tables.Shift.AndPackedPilot
import Airbender.Data.Tables.Shift.AndData
import Airbender.Proofs.Tables.PackedBytes

namespace Airbender.Verification.PackedImportPilot
open Airbender.Setup.Proofs.PackedBytes
set_option warningAsError true

def indexPacked : Nat := 0xfffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0bfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100
def repeatedOnes : Nat := 0x1010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101
def expectedRow (row : Nat) : Nat := indexPacked &&& (row * repeatedOnes)
def check (data : Array Nat) : Bool := checkRows data 256 expectedRow

def Fact (data : Array Nat) : Prop :=
  ∀ row column, row < 256 → column < 256 →
    (data[row]?.map fun packed => (packed / 256 ^ column) % 256) =
      some (row &&& column)

set_option maxRecDepth 131072
set_option maxHeartbeats 0
theorem index_correct : indexPacked = Nat.ofDigits 256 (List.range 256) := by decide +kernel
theorem ones_correct : repeatedOnes = Nat.ofDigits 256 (List.replicate 256 1) := by decide +kernel
theorem ok : check byteAndPackedPilot = true := by decide +kernel

theorem expectedRow_byte (row column : Nat) (hr : row < 256) (hc : column < 256) :
    (expectedRow row / 256 ^ column) % 256 = row &&& column := by
  have hindex : (indexPacked / 256 ^ column) % 256 = column := by
    rw [index_correct, Airbender.Setup.Proofs.PackedBytes.extractDigit]
    · simp [hc]
    · intro digit hd
      exact List.mem_range.mp hd
    · simpa using hc
  have hrow : ((row * repeatedOnes) / 256 ^ column) % 256 = row := by
    rw [ones_correct, Nat.mul_ofDigits]
    simp only [List.map_replicate, mul_one]
    rw [Airbender.Setup.Proofs.PackedBytes.extractDigit]
    · exact List.getElem_replicate (by simpa using hc)
    · intro digit hd
      exact (List.eq_of_mem_replicate hd).symm ▸ hr
  rw [expectedRow, Airbender.Setup.Proofs.PackedBytes.extractAnd, hindex, hrow,
    Nat.and_comm]

/-- Once-proved semantic soundness for any packed capture; `ok` is the only
capture-specific Boolean proof. -/
theorem check_sound (data : Array Nat) (h : check data = true) : Fact data := by
  intro row column hr hc
  have hrow := checkRows_sound data 256 expectedRow h ⟨row, hr⟩
  rw [hrow]
  exact congrArg some (expectedRow_byte row column hr hc)

/-- The checked packed capture has the expected output at every native row.
The existing Block column certificate remains in force until consumers migrate. -/
theorem and_outputs_packed : Fact byteAndPackedPilot := check_sound _ ok

/-- Both import paths retain the same full native setup artifact bytes. The
source parser and region slicing remain the explicit importer trust boundary. -/
theorem same_source_bytes :
    byteAndPackedPilotSourceBytes = byteAndDataSourceBytes := rfl

end Airbender.Verification.PackedImportPilot
