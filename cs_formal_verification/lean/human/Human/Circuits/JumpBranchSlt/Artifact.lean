module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Human.Helpers.Core.CircuitOutput

@[expose] public section

namespace Airbender.JumpBranchSlt

namespace Branch

end Branch

-- Retained assertions, word/comparison queries and native trace metadata.
-- Fixed-table correspondence and logical matching enforcement remain external.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit comparison_lookups trace_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime], importedCircuit.operations .comparison = .ok (importedConstraints (p := p))) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.traceColumns = .ok importedConstraintsTraceColumns ∧
  importedCircuit.memoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.decoderColumns = .ok importedConstraintsDecoderColumns

/-- Original retained constraints plus the eight native timestamp queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

-- Named columns used by the review contracts. ArtifactChecks verifies their
-- locations; the decoder interface supplies the selectors' meaning.
namespace Variables
abbrev initialPCLo : Nat := 0
abbrev initialPCHi : Nat := 1
abbrev execute : Nat := 4
abbrev rs1Index : Nat := 5
abbrev rs2Index : Nat := 6
abbrev rdIndex : Nat := 7
abbrev immediateLo : Nat := 8
abbrev immediateHi : Nat := 9
abbrev conditionTag : Nat := 10
abbrev jalSelector : Nat := 11
abbrev jalrSelector : Nat := 12
abbrev comparisonSelector : Nat := 13
abbrev branchSelector : Nat := 14
abbrev discardedSelector : Nat := 15
abbrev finalPCLo : Nat := 16
abbrev finalPCHi : Nat := 17
abbrev rs1Lo : Nat := 22
abbrev rs1Hi : Nat := 23
abbrev rs2Lo : Nat := 26
abbrev rs2Hi : Nat := 27
abbrev destinationLo : Nat := 30
abbrev destinationHi : Nat := 31
end Variables

end Airbender.JumpBranchSlt
