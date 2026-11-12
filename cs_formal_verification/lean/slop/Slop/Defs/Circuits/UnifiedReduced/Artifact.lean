module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Human.Circuits.UnifiedReduced.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/UnifiedReduced/Artifact.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.UnifiedReduced
set_option maxRecDepth 8192
namespace Variables
abbrev dispatchColumns := #v[11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29]
end Variables
end Airbender.UnifiedReduced
