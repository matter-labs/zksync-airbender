module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Human.Helpers.Core.Word

@[expose] public section

namespace Airbender.AddSub
open Arithmetic

-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"
-- Its equations, range queries and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit trace_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact;
    and the artifact pads its decoder lookups with -1 (canonical p - 1), not 0, as the Rust compiler sets for this
    family (`cs/src/gkr_compiler/family_circuit.rs`): no phantom all-zero decoder row (docs/TRUST_AND_REVIEW.md,
    decoder-table padding). -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime], importedCircuit.operations .addSub = .ok (importedConstraints (p := p))) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.traceColumns = .ok importedConstraintsTraceColumns ∧
  importedCircuit.memoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.decoderColumns = .ok importedConstraintsDecoderColumns ∧
  importedCircuit.generic_lookup_padding.map (·.canonical.val) = some (babyBearModulus - 1)

/-- Arithmetic, word ranges and the eight native timestamp queries. Decoder and
    global state/memory matching are separate trace obligations. -/
def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

/-- PC limbs in the imported artifact. Initial bounds come from the state interface;
    final bounds are enforced by the imported lookups. -/
structure PCMapping {p : Nat} (initial final : Word) (w : Nat → ZMod p) : Prop where
  initialLo : w 0 = (initial.lo : ZMod p)
  initialHi : w 1 = (initial.hi : ZMod p)
  finalLo : final.lo = (w 19).val
  finalHi : final.hi = (w 20).val

end Airbender.AddSub
