import Airbender.Proofs.Trace.Families.WordMemory.ShadowImage
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Trace

/-- Architectural cell transfers omit readonly native ROM-shadow addresses.
    Separate public shadow seeds stay in full native matching; Sail needs no
    shadow read or shadow/ROM value equality. Physical boot/ROM-table binding
    and original LOAD/STORE instruction execution remain separate. -/
theorem public_projected_sail_history {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row mersenne31Modulus WordMemoryFamily))
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after :=
  Proofs.projected_row_history (by decide) inputs accepted decoded aligned

end Airbender.WordMemory
