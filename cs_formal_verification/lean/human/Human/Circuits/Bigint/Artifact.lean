module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Airbender.Bigint

set_option maxRecDepth 16384

-- All native equations, ranges and fixed queries. Setup rows remain an interface.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/bigint_with_extended_control_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit bigint_lookups delegation_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 3)),
    importedCircuit.tableOperations .bigint table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.delegationColumns = .ok importedConstraintsDelegationColumns ∧
  importedCircuit.delegationPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.indirectPorts = .ok importedConstraintsIndirectPorts.toArray

/-- Native invocation ranges and every timestamp comparison, in addition to
    the family's retained equations and modeled table queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints setup ++ importedConstraintsTimestampLookups

namespace Variables
abbrev controlBits := #v[59, 60, 61, 62, 63, 64, 65, 66]
-- Same order as common_constants/src/delegation_types/bigint_with_control.rs;
-- carry is bit six and is excluded from opcode exclusivity.
abbrev operations := #v[59, 60, 61, 62, 63, 64, 66]
def leftLimbs : Vector Nat 16 := Vector.ofFn fun i => 5 + 4 * (i.val / 2) + i.val % 2
def rightLimbs : Vector Nat 16 := Vector.ofFn fun i => 39 + i.val
def writtenLimbs : Vector Nat 16 := Vector.ofFn fun i => 7 + 4 * (i.val / 2) + i.val % 2
end Variables

end Airbender.Bigint
