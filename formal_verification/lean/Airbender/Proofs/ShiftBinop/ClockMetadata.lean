import Airbender.Proofs.ShiftBinop.ArtifactChecks

namespace Airbender.ShiftBinop.Proofs
set_option autoImplicit false

theorem setup_columns : importedConstraintsSetupColumns =
    (⟨16777216,16,0,1,2,1,6,1048576,10817537⟩ : Verification.SetupColumns) := rfl

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5,6,7,8,#v[9,10],11,12⟩ : Trace.DecoderColumns) := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4,#v[0,1],#v[13,14],#v[2,3],#v[15,16],
      #[⟨0,#v[65,66],67⟩,⟨1,#v[68,69],70⟩,⟨2,#v[71,72],73⟩]⟩ : Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0,#v[65,66],67⟩,.register 5,#v[23,24],none⟩,
       ⟨⟨1,#v[68,69],70⟩,.register 6,#v[25,26],none⟩,
       ⟨⟨2,#v[71,72],73⟩,.register 7,#v[57,58],some #v[59,60]⟩] : Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts,importedConstraintsTraceColumns]

end Airbender.ShiftBinop.Proofs
