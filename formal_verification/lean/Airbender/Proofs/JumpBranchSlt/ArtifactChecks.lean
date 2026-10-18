import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt.Proofs

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 36 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 16 := rfl

theorem setup_columns : importedConstraintsSetupColumns =
    (⟨16777216, 16, 0, 1, 2, 1, 6, 1048576, 65664⟩ : Verification.SetupColumns) := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0, 1], #v[13, 14], #v[2, 3], #v[15, 16],
      #[⟨0, #v[51, 52], 53⟩, ⟨1, #v[54, 55], 56⟩, ⟨2, #v[57, 58], 59⟩]⟩ :
      Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0, #v[51, 52], 53⟩, .register 5, #v[22, 23], none⟩,
       ⟨⟨1, #v[54, 55], 56⟩, .register 6, #v[24, 25], none⟩,
       ⟨⟨2, #v[57, 58], 59⟩, .register 7, #v[40, 41], some #v[38, 39]⟩] :
       Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5, 6, 7, 8, #v[9, 10], 11, 12⟩ : Trace.DecoderColumns) := rfl

end Airbender.JumpBranchSlt.Proofs
