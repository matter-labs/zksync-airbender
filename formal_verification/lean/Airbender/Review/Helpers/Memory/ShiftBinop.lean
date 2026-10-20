import Airbender.Review.Helpers.Memory.SailHistory
import Airbender.Review.Helpers.Decoder.ShiftBinop

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Trace Reference.RiscV.Sail Reference.Sail

/-- Actual original Sail GPR observations for one native row. All reads use the
    same pre-state; the final write uses the actual native masked write word. -/
def RegisterTransfer {p : Nat} (row : Row p ShiftBinopFamily) (entry : ProgramEntry)
    (before after : State) : Prop :=
  (∀ i : Fin 3, run (SailRV32.Functions.rX_bits
      (.Regidx (#v[entry.data.rs1,entry.data.rs2,entry.data.rd])[i])) before =
    .ok (memoryWord (importedConstraintsMemoryPorts[i].readCode row.assignment)) before) ∧
  run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
    (memoryWord (importedConstraintsMemoryPorts[2].writeCode row.assignment))) before =
      .ok () after

/-- Observable initialized native GPR realization. Segment states, original
    decoding in each real pre-state, code/configuration frames and final cell
    matching are conclusions. Original operation/PC execution is separate. -/
def RegisterHistory {p : Nat} [Fact p.Prime] (trace : Data p ShiftBinopFamily)
    (setup : SparseDecoderSetup Operation) (initial : State) (cells : List Cell) : Prop :=
  ∃ (history : TimestampSortedMemoryAccessList)
    (rows : List (Row p ShiftBinopFamily)) (after : State),
    MemoryHistory trace history ∧ rows.Perm trace.rows ∧
    rows.Pairwise (fun a b => b.clock < a.clock) ∧
    SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
      initial after ∧ SailStateMatches cells history after ∧
    after.mem = initial.mem ∧ after.regs.get? .misa = initial.regs.get? .misa ∧
    ∀ newer row older, rows = newer ++ row :: older →
      ∃ entry ∈ setup.program, ∃ rowBefore rowAfter,
        entry.SourceWith initial decoderFields ∧ entry.SourceWith rowBefore decoderFields ∧
        row.decoderQuery = entry.query ∧
        SailHistory cells (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
          initial rowBefore ∧
        SailHistory cells (rowEvents trace.memoryEpoch row).reverse rowBefore rowAfter ∧
        SailHistory cells (newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
          rowAfter after ∧ RegisterTransfer row entry rowBefore rowAfter

end Airbender.ShiftBinop
