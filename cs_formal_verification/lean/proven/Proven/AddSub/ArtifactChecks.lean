module
public import Human.Circuits.AddSub.Artifact
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.AddSub

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := by rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 30 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 6 := by rfl

end Airbender.AddSub
