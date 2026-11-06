import Slop.Trace.Family.Timestamps
import Slop.Trace.RowHistory
import Slop.Trace.Family.History
import Slop.Trace.Family.ZeroRegister

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]
open Reference.RiscV.Sail

/-- Group the already-derived Sail transfers into complete instruction rows.
    Initial state, public bytes and native logical matching remain the inputs. -/
theorem decoded_row_history [Fact p.Prime]
    {projection : SailRV32.instruction → Option DecoderData} (rules : DecoderRules projection) (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (programImage : Trace.programImageWith projection before addresses = some program)
    (decoded : Decoded trace program)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured before := by find_configured) :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row p)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => rowClock b < rowClock a) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
        before after ∧ SailStateMatches cells history after := by
  exact native_row_history hp inverse accepted boundary image domain aligned
    (native_zero_writes rules hp inverse accepted boundary image programImage decoded)

end Airbender.Trace.Proofs
