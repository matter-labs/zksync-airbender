import Airbender.Data.Tables.Shift.AndPackedPilot
import Airbender.Data.Tables.Shift.AndData
import Airbender.Proofs.Tables.PackedBitwise

namespace Airbender.Verification.PackedImportPilot
open Airbender.Setup.Proofs.PackedBitwise
set_option warningAsError true

def expectedRow (row : Nat) : Nat :=
  Airbender.Setup.Proofs.PackedBitwise.expectedRow .bitAnd row
def check (data : Array Nat) : Bool :=
  Airbender.Setup.Proofs.PackedBitwise.check .bitAnd data

def Fact (data : Array Nat) : Prop :=
  Airbender.Setup.Proofs.PackedBitwise.Fact .bitAnd data

set_option maxRecDepth 131072
set_option maxHeartbeats 0
theorem ok : check byteAndPackedPilot = true := by decide +kernel

theorem expectedRow_byte (row column : Nat) (hr : row < 256) (hc : column < 256) :
    (expectedRow row / 256 ^ column) % 256 = row &&& column := by
  exact Airbender.Setup.Proofs.PackedBitwise.expected_byte .bitAnd row column hr hc

/-- Once-proved semantic soundness for any packed capture; `ok` is the only
capture-specific Boolean proof. -/
theorem check_sound (data : Array Nat) (h : check data = true) : Fact data := by
  exact Airbender.Setup.Proofs.PackedBitwise.check_sound .bitAnd data h

/-- The checked packed capture has the expected output at every native row.
The existing Block column certificate remains in force until consumers migrate. -/
theorem and_outputs_packed : Fact byteAndPackedPilot := check_sound _ ok

/-- Both import paths retain the same full native setup artifact bytes. The
source parser and region slicing remain the explicit importer trust boundary. -/
theorem same_source_bytes :
    byteAndPackedPilotSourceBytes = byteAndDataSourceBytes := rfl

end Airbender.Verification.PackedImportPilot
