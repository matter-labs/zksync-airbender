module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.UnifiedReduced

-- All retained equations, ranges and five pooled lookup sets. The caller supplies
-- the tagged setup table; decoder and global memory arguments remain external.
set_option maxRecDepth 8192
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit unified_reduced_lookups trace_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 10)),
    importedCircuit.tableOperations .unifiedReduced table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.traceColumns = .ok importedConstraintsTraceColumns ∧
  importedCircuit.memoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.decoderColumns = .ok importedConstraintsDecoderColumns

/-- Retained equations, modeled setup queries and the eight native clock queries.
    Decoder membership and global state/memory matching are separate obligations. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev jalSelector := 21
abbrev jalrSelector := 22
abbrev comparisonSelector := 23
abbrev branchSelector := 24
abbrev finalPCLo := 30
abbrev finalPCHi := 31
abbrev pcCarry := 122
abbrev dispatchColumns := #v[11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29]
end Variables

end Airbender.UnifiedReduced
