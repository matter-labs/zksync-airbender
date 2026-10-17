import Airbender.Proofs.Trace.Families.WordMemory.History
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Trace

/-- Actual public seed reads and native matching yield complete Clean memory
    consistency and newest preceding reads for all three v2 word-memory ports.
    This includes readonly ROM-shadow accesses. Their architectural projection
    and instruction execution remain separate. -/
theorem public_memory_soundness {trace : Data mersenne31Modulus WordMemoryFamily}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace) :
    (∃ history, MemoryHistory trace history) ∧
      ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  ⟨Trace.Proofs.native_memory_history (by decide) accepted
      (Trace.Proofs.image_clock_boundary (by decide) inputs)
      (Trace.Proofs.image_unique inputs.image inputs.domain),
    Trace.Proofs.latest_reads (by decide) accepted
      (Trace.Proofs.image_clock_boundary (by decide) inputs)
      (Trace.Proofs.image_unique inputs.image inputs.domain)⟩

end Airbender.WordMemory
