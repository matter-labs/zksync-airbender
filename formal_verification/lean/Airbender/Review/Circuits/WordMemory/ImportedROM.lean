import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Tables.ImportedROMReads

namespace Airbender.WordMemory

/-- The existing ROM-read interface is a conclusion of actual imported table
    membership and public image binding. No expected witness value or table
    equivalence is supplied by the caller. -/
theorem imported_rom_soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {initial : Reference.RiscV.Sail.State} (image : Trace.ROM.ImportedImage initial) :
    Trace.ROM.Reads initial (Trace.ROM.importedTable (p := p)) :=
  Trace.ROM.Proofs.imported_reads hp image

end Airbender.WordMemory
