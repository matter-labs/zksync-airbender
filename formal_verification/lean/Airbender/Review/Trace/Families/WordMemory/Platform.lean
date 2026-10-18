import Airbender.Proofs.Trace.Families.WordMemory.MemoryTransport
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Trace Reference.RiscV.Sail

/-- Initialized architectural transfers preserve the public Machine/PMP/PMA
    configuration. Native shadow matching is retained. Original instruction
    execution, physical boot/profile and cryptographic enforcement are separate. -/
theorem public_projected_platform_configuration
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup} {before : State}
    {cells : List Cell} {seeds : List ShadowSeed}
    (inputs : ShadowImageBoundary trace before cells seeds) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (configuration : FlatMemoryConfiguration before) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus WordMemoryFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) before after ∧
      SailStateMatches cells history after ∧ FlatMemoryConfiguration after :=
  Proofs.projected_platform_configuration (by decide) inputs accepted decoded aligned configuration

end Airbender.WordMemory
