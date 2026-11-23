module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.Keccak.Split.ColumnParity

set_option maxRecDepth 16384

/- The no-cache column-parity worker (CSR 0x7CD): its equations, the timestamp
   alignment query and all 22 fixed-table queries over the supplied setup, plus its
   delegation clock and memory-port metadata. Each port has its own borrowed
   timestamp comparison, as in the other delegation workers. -/
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_column_parity_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit keccak_column_parity_lookups delegation_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 8)),
    importedCircuit.tableOperations .keccakColumnParity table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.delegationColumns = .ok importedConstraintsDelegationColumns ∧
  importedCircuit.delegationPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.indirectPorts = .ok importedConstraintsIndirectPorts.toArray

/-- The operation core plus the invocation and timestamp-comparison queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ColumnParity
