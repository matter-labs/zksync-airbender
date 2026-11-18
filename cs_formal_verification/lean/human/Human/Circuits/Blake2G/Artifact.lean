module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.Blake2G

-- The supplied tagged setup is an explicit interface, not a witness-generation hint.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/blake2_g_function_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit blake_g_lookups delegation_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 9)),
    importedCircuit.tableOperations .blakeG table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.delegationColumns = .ok importedConstraintsDelegationColumns ∧
  importedCircuit.delegationPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.indirectPorts = .ok importedConstraintsIndirectPorts.toArray

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev execute := 0
end Variables

end Airbender.Blake2G
