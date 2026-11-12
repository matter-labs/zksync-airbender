module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Human.Circuits.Blake2G.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2G/Artifact.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2G
namespace Variables
abbrev controlReadLo := 3
abbrev controlReadHi := 4
abbrev controlWriteLo := 5
abbrev controlWriteHi := 6
abbrev stateOffsetColumns := #v[7, 8, 9, 10]
abbrev messageOffsetColumns := #v[11, 12]
abbrev statePointerLo := 13
abbrev messagePointerLo := 31
abbrev booleanColumns := #v[0, 37, 38, 39, 40, 49, 50, 65, 66, 67, 68, 75, 76,
  85, 88, 91, 94, 97, 100, 103, 106, 109]
end Variables
end Airbender.Blake2G
