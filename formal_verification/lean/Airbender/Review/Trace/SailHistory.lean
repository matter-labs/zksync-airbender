import Airbender.Proofs.Mersenne31
import Airbender.Proofs.Trace.ZeroRegister

namespace Airbender.Trace

/-- Public Sail seeds, native acceptance and complete logical decoder membership
    construct actual Sail cell reads/writes for every native transfer. Only public
    RAM-cell alignment is supplied; intermediate states and x0 values are derived.
    Instruction execution and physical setup/cryptographic enforcement are separate. -/
theorem public_image_sail_history {trace : Data mersenne31Modulus} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (seed : TimestampSortedMemoryAccessList) (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧ SailHistory cells events before after ∧
      SailStateMatches cells history after :=
  Proofs.image_sail_history (by decide) inputs accepted decoded aligned

end Airbender.Trace
