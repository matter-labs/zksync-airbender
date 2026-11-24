module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Airbender.Blake2Round

set_option maxRecDepth 16384

-- Native Clean equations and queries; setup provenance and memory transport remain external.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/blake2_with_extended_control_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit blake_round_lookups delegation_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 6)),
    importedCircuit.tableOperations .blakeRound table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.delegationColumns = .ok importedConstraintsDelegationColumns ∧
  importedCircuit.delegationPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.indirectPorts = .ok importedConstraintsIndirectPorts.toArray

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev controlBits := #v[139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
abbrev roundBits := #v[142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
end Variables

end Airbender.Blake2Round
