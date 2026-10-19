import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.MulDiv.Proofs

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 49 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 20 := rfl

theorem setup_columns : importedConstraintsSetupColumns =
    (⟨16777216,16,0,1,2,1,6,1048576,65536⟩ : Verification.SetupColumns) := rfl

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5,6,7,8,#v[9,10],11,12⟩ : Trace.DecoderColumns) := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4,#v[0,1],#v[13,14],#v[2,3],#v[15,16],
      #[⟨0,#v[66,67],68⟩,⟨1,#v[69,70],71⟩,⟨2,#v[72,73],74⟩]⟩ : Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0,#v[66,67],68⟩,.register 5,#v[19,20],none⟩,
       ⟨⟨1,#v[69,70],71⟩,.register 6,#v[21,22],none⟩,
       ⟨⟨2,#v[72,73],74⟩,.register 7,#v[58,59],some #v[60,61]⟩] : Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts,importedConstraintsTraceColumns]

end Airbender.MulDiv.Proofs
