import Airbender.Proofs.Trace.Families.WordMemory.PortReads
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Trace

/-- Public seeds, accepted native matching and full decoder membership derive
    actual Sail cell reads/writes and intermediate states in native clock order.
    The full supplied native RAM domain includes shadow cells. Architectural ROM
    projection, original instruction execution and physical boot remain separate. -/
theorem public_sail_cell_history {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row mersenne31Modulus WordMemoryFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        before after ∧ SailStateMatches cells history after :=
  Proofs.image_row_history (by decide) inputs accepted decoded aligned

end Airbender.WordMemory
