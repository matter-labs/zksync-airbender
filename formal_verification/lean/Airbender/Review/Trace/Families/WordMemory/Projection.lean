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

/-- Separate architectural/shadow initialization also bounds every full native
    read, actual write and terminal token, including erased shadow accesses. -/
theorem public_projected_value_bounds {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.shadow_value_bounds (by decide) inputs accepted decoded

end Airbender.WordMemory
