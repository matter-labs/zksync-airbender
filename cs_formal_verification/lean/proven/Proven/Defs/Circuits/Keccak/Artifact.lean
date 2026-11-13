module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Human.Circuits.Keccak.Artifact
public import Proven.CleanCore.Circuit.Operations

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Keccak/Artifact.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Keccak
set_option maxRecDepth 16384
theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 42 := by rfl
namespace Variables
abbrev controlReadLo := 3
abbrev controlReadHi := 4
abbrev controlWriteLo := 5
abbrev controlWriteHi := 6
abbrev modeColumns := #v[63, 64, 65, 66, 67, 68, 69]
abbrev iterationColumns := #v[70, 71, 72, 73, 74]
abbrev roundColumns := #v[75, 76, 77, 78, 79]
end Variables
end Airbender.Keccak
