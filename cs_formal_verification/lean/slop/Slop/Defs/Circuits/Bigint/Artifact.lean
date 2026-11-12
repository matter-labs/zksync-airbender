module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Mathlib.Tactic.FinCases
public import Human.Circuits.Bigint.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Bigint/Artifact.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Bigint
set_option maxRecDepth 16384
namespace Variables
abbrev controlBits := #v[59, 60, 61, 62, 63, 64, 65, 66]
end Variables
end Airbender.Bigint
