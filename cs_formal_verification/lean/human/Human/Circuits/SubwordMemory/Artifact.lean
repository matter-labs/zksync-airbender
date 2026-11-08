module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.SubwordMemory

-- All retained equations, five ranges and both non-decoder lookup sets.
-- The tagged setup table is caller-supplied; its fixed/ROM semantics and
-- program/setup binding are separate obligations. RAM load/store claims are in Theorems.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/mem_subword_only_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit subword_memory_lookups trace_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 9)),
    importedCircuit.tableOperations .subwordMemory table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.traceColumns = .ok importedConstraintsTraceColumns ∧
  importedCircuit.memoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.decoderColumns = .ok importedConstraintsDecoderColumns

def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev storeSelector := 10
abbrev byteSelector := 11
abbrev signedSelector := 12
abbrev finalPCLo := 13
abbrev finalPCHi := 14
end Variables

end Airbender.SubwordMemory
