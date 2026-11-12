module
public import Human.Circuits.WordMemory.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.WordMemory

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := by rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (importedConstraints rom)).length = 27 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (importedConstraints rom)).length = 4 := by rfl

end Airbender.WordMemory
