import Airbender.Review.Circuits.UnifiedReduced.Decoder
import Airbender.Review.Trace.Execution
import Airbender.Review.Helpers.SailHistory

namespace Airbender.UnifiedReduced
open Trace

/-- The unified circuit's native accesses execute as actual Sail cell reads and
    writes from the public starting state. `rows` contains every imported row
    once, in reverse clock order. Each row's accesses remain grouped in native
    port order, including aliases; the final Sail cells realize Clean's latest
    values. This is memory transport, not yet original instruction retirement. -/
def MemoryExecution [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : Reference.RiscV.Sail.State) (cells : List Cell) : Prop :=
  ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Trace.Row p UnifiedFamily))
    (final : Reference.RiscV.Sail.State),
    MemoryHistory trace history ∧ rows.Perm trace.rows ∧
    rows.Pairwise (fun a b => b.clock < a.clock) ∧
    SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial final ∧
    SailStateMatches cells history final

end Airbender.UnifiedReduced
