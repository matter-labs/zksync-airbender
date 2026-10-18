import Airbender.Proofs.Trace.Families.JumpBranchSlt.History
import Airbender.Proofs.Mersenne31

namespace Airbender.JumpBranchSlt
open Trace

/-- Actual public seed reads and native matching yield complete Clean memory
    consistency and newest preceding reads for all three v2 control ports.
    Readonly alias refreshes and the actual masked destination write remain in
    matching. Word bounds and original Sail cell/instruction execution are separate. -/
theorem public_memory_soundness {trace : Data mersenne31Modulus JumpBranchSltFamily}
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

end Airbender.JumpBranchSlt
