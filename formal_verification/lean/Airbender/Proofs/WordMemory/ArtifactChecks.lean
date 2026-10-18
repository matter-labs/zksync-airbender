import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.WordMemory.Proofs

theorem constraint_count {p : Nat} [Fact p.Prime] (rom : Verification.WordROM) :
    (FlatOperation.constraints (importedConstraints (p := p) rom)).length = 35 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (rom : Verification.WordROM) :
    (FlatOperation.lookups (importedConstraints (p := p) rom)).length = 12 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[13, 14], #v[2, 3], #v[15, 16],
      #[⟨0, #v[47, 48], 49⟩, ⟨1, #v[50, 51], 52⟩, ⟨2, #v[53, 54], 55⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[47, 48], 49⟩, .register 5, #v[17, 18], none⟩,
       ⟨⟨1, #v[50, 51], 52⟩, .mixed 12 true #v[28, 29], #v[30, 31], none⟩,
       ⟨⟨2, #v[53, 54], 55⟩, .mixed 32 true #v[33, 34], #v[35, 36], some #v[37, 38]⟩] :
       Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, 8, #v[9, 10], 11, 12⟩ : Trace.DecoderColumns) := rfl

/-- Native generic tuple width includes its tag; decoder begins after it. -/
theorem setup_columns : importedConstraintsSetupColumns =
    (⟨16777216, 16, 0, 1, 2, 1, 6, 1048576, 1114113⟩ : Verification.SetupColumns) := rfl

end Airbender.WordMemory.Proofs
