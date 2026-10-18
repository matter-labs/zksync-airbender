import Airbender.Proofs.Trace.Families.WordMemory.CodeHistory
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Trace Verification

/-- Initialized projected transfers preserve every byte in the native ROM
    prefix and every successful public ROM extraction. Public programs fitting
    that region retain original Sail reads/decoding. Missing bytes stay missing;
    physical boot/export and original instruction execution are separate. -/
theorem public_projected_rom_preservation {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus WordMemoryFamily)) (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after ∧
      (∀ key < 4194304, after.mem[key]? = before.mem[key]?) ∧
      (∀ {count rom}, wordROMImage before count = some rom → wordROMImage after count = some rom) ∧
      (∀ {count logCapacity}, decoderSetupImage before count logCapacity = some setup →
        count ≤ 1048576 → ∀ entry ∈ setup.program, entry.SourceWith after decoderFields) :=
  Proofs.projected_rom_preservation (by decide) inputs accepted decoded aligned

end Airbender.WordMemory
