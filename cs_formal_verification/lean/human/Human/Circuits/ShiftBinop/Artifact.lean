module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.ShiftBinop

inductive Operation where
  | xor | or | and | sll | srl | sra | rev8
  deriving DecidableEq

def Operation.tag : Operation → Nat
  | .xor => 4 | .or => 6 | .and => 7
  | .sll => 1 | .srl => 2 | .sra => 3 | .rev8 => 5

def Operation.isShift : Operation → Bool
  | .sll | .srl | .sra | .rev8 => true
  | _ => false

-- All retained equations, both range queries and all five dynamic-tag lookups.
-- Native trace/decoder metadata is imported; logical matching and setup fidelity
-- remain external boundaries.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/shift_binop_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit shift_binop_lookups trace_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime], importedCircuit.operations .shiftBinop = .ok (importedConstraints (p := p))) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.traceColumns = .ok importedConstraintsTraceColumns ∧
  importedCircuit.memoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.decoderColumns = .ok importedConstraintsDecoderColumns

def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

end Airbender.ShiftBinop
