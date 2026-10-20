import Airbender.Review.Circuits.SubwordMemory.Artifact

namespace Airbender.SubwordMemory.Proofs
set_option autoImplicit false

theorem constraint_count {p : Nat} [Fact p.Prime] (rom : Verification.WordROM) :
    (FlatOperation.constraints (importedConstraints (p := p) rom)).length = 51 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (rom : Verification.WordROM) :
    (FlatOperation.lookups (importedConstraints (p := p) rom)).length = 14 := rfl

theorem clock_columns : importedConstraintsTraceColumns =
    (⟨4, #v[0,1], #v[13,14], #v[2,3], #v[15,16],
      #[⟨0,#v[68,69],70⟩,⟨1,#v[71,72],73⟩,⟨2,#v[74,75],76⟩]⟩ : Trace.TraceColumns) := rfl

theorem memory_ports : importedConstraintsMemoryPorts =
    (#[⟨⟨0,#v[68,69],70⟩,.register 5,.u16 #v[17,18],none⟩,
       ⟨⟨1,#v[71,72],73⟩,.mixed 12 true #v[30,31],.u16 #v[32,33],none⟩,
       ⟨⟨2,#v[74,75],76⟩,.mixed 34 true #v[35,36],.u16 #v[37,38],some (.u16 #v[39,40])⟩] :
       Array Trace.MemoryPort) := rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5,6,7,8,#v[9,10],11,12⟩ : Trace.DecoderColumns) := rfl

theorem setup_columns : importedConstraintsSetupColumns =
    (⟨16777216,16,0,1,2,1,6,1048576,9502721⟩ : Verification.SetupColumns) := rfl

end Airbender.SubwordMemory.Proofs
