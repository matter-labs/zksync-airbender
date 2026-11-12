module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.Keccak.Split.ThetaRho

set_option maxRecDepth 16384

/- The no-cache theta+rho worker (CSR 0x7CC): its equations (including the grouped
   timestamp equations), the alignment query and all 50 fixed-table queries over the
   supplied setup, plus its grouped clock and memory-port metadata. -/
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/keccak_theta_rho_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit keccak_theta_rho_lookups split_delegation_timestamps

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 9)),
    importedCircuit.tableOperations .keccakThetaRho table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.splitTimestampGroups = .ok importedConstraintsTimestampGroups ∧
  importedCircuit.splitDelegationColumns = .ok importedConstraintsDelegationColumns ∧
  importedCircuit.splitMemoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.indirectPorts = .ok importedConstraintsIndirectPorts.toArray

/-- The operation core plus the invocation timestamp query. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

end Airbender.Keccak.Split.ThetaRho
