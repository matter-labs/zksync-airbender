import Airbender.Review.Circuits.AddSub.Artifact

namespace Airbender.AddSub.Proofs

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 37 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 12 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[13, 14], #v[2, 3], #v[15, 16],
      #[⟨0, #v[44, 45], 46⟩, ⟨1, #v[47, 48], 49⟩, ⟨2, #v[50, 51], 52⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[44, 45], 46⟩, .register 5, #v[25, 26], none⟩,
       ⟨⟨1, #v[47, 48], 49⟩, .register 6, #v[27, 28], none⟩,
       ⟨⟨2, #v[50, 51], 52⟩, .register 7, #v[35, 36], some #v[37, 38]⟩] :
       Array Trace.MemoryPort) := rfl

end Airbender.AddSub.Proofs
