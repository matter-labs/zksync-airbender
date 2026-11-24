module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.Keccak.Split.Chi5

set_option maxRecDepth 16384

/- The no-cache chi worker (CSR 0x7CE): its equations (including the grouped
   timestamp equations), the alignment query and all 17 fixed-table queries over the
   supplied setup, plus its grouped clock and memory-port metadata. -/
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_chi5_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit keccak_chi5_lookups split_delegation_timestamps

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 11)),
    importedCircuit.tableOperations .keccakChi5 table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.splitTimestampGroups = .ok importedConstraintsTimestampGroups ∧
  importedCircuit.splitDelegationColumns = .ok importedConstraintsDelegationColumns ∧
  importedCircuit.splitMemoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.indirectPorts = .ok importedConstraintsIndirectPorts.toArray

/-- The operation core plus the invocation timestamp query. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 11)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.Chi5
