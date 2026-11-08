module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations

@[expose] public section

namespace Airbender.WordMemory

-- All retained equations, three range queries, and the conditional ROM query.
-- The caller supplies the native Clean ROM table; its program/setup binding is
-- an explicit interface, and table extraction remains deferred.
-- The artifact, transcribed (trusted: `Human/Import/TranscribeCommand.lean`).
import_circuit importedCircuit from "../../cs/compiled_circuits/mem_word_only_layout_no_caches_gkr.json"
-- Its operations and column metadata as literal terms, fixed by `ArtifactImportClaim`.
import_clean importedConstraints from importedCircuit word_memory_lookups trace_metadata

/-- The imported definitions are the meaning (`Human/Import/Operations.lean`, `Columns.lean`) of the artifact. -/
def ArtifactImportClaim : Prop :=
  (∀ (p : Nat) [Fact p.Prime] (table : Table (ZMod p) (fields 9)),
    importedCircuit.tableOperations .wordMemory table = .ok (importedConstraints table)) ∧
  (∀ (p : Nat) [Fact p.Prime],
    importedCircuit.timestampOperations = .ok (importedConstraintsTimestampLookups (p := p))) ∧
  importedCircuit.traceColumns = .ok importedConstraintsTraceColumns ∧
  importedCircuit.memoryPorts = .ok importedConstraintsMemoryPorts ∧
  importedCircuit.decoderColumns = .ok importedConstraintsDecoderColumns

def clockConstraints {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  importedConstraints rom ++ importedConstraintsTimestampLookups

namespace Variables
abbrev initialPCLo := 0
abbrev initialPCHi := 1
abbrev execute := 4
abbrev rs1Index := 5
abbrev rs2Index := 6
abbrev rdIndex := 7
abbrev immediateLo := 8
abbrev immediateHi := 9
abbrev storeSelector := 10
abbrev finalPCLo := 11
abbrev finalPCHi := 12
abbrev sourceLo := 17
abbrev sourceHi := 18
abbrev readAddressLo := 19
abbrev readAddressHi := 20
abbrev readDataLo := 23
abbrev readDataHi := 24
abbrev writeAddressLo := 25
abbrev writeAddressHi := 26
abbrev writeDataLo := 31
abbrev writeDataHi := 32
abbrev romSelector := 35
end Variables

end Airbender.WordMemory
