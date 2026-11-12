module
public import Human.Circuits.UnifiedReduced.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.UnifiedReduced

set_option maxRecDepth 8192

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := by rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.constraints (importedConstraints setup)).length = 120 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.lookups (importedConstraints setup)).length = 18 := by rfl

end Airbender.UnifiedReduced
