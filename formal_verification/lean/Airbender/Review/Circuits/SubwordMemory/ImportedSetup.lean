import Airbender.Proofs.Tables.ImportedSubwordROM

namespace Airbender.SubwordMemory

/-- Actual native fixed and ROM rows supply the existing subword table under
    public image binding. Existing lookup and instruction proofs can use this
    equality as a conclusion, without assuming table-content correspondence. -/
theorem imported_setup_soundness {p : Nat} [Fact p.Prime]
    {initial : Reference.RiscV.Sail.State} (image : Trace.ROM.ImportedImage initial) :
    Verification.importedSubwordTable (p := p) =
      Verification.subwordTable (Trace.ROM.words initial) :=
  Verification.SubwordROMGeometry.imported_subword_table_before image

end Airbender.SubwordMemory
