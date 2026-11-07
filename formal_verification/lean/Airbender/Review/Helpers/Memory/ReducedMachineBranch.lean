import Airbender.Review.Helpers.Memory.SailHistory
import Airbender.Review.Helpers.Decoder.ReducedMachineBranch

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail Reference.Sail
set_option autoImplicit false

/-- Original GPR observations and the actual native masked write. All source
    and old-destination reads observe the same pre-state, including aliases. -/
def BranchRegisterTransfer (row : Row mersenne31Modulus NativeReducedFamily)
    (entry : BranchProgramEntry) (before after : State) : Prop :=
  (∀ i : Fin 3, run (SailRV32.Functions.rX_bits
      (.Regidx (#v[entry.data.rs1,entry.data.rs2,entry.data.rd])[i])) before =
    .ok (memoryWord (importedConstraintsMemoryPorts[i].readCode row.assignment)) before) ∧
  run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
    (memoryWord (importedConstraintsMemoryPorts[2].writeCode row.assignment))) before = .ok () after ∧ after = before

/-- Observable initialized original Sail realization for selected native branches.
    States/order/reads/writes/decoder replay and final matching are conclusions.
    Numerical PC, original executed clauses and physical setup remain separate. -/
def BranchRegisterHistory (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup BranchMode) (initial : State) (cells : List Cell) : Prop :=
  ∃ (history : TimestampSortedMemoryAccessList)
    (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : State),
    MemoryHistory trace history ∧ rows.Perm trace.rows ∧
    rows.Pairwise (fun a b => b.clock < a.clock) ∧
    SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
      initial after ∧ SailStateMatches cells history after ∧
    after.mem = initial.mem ∧ after.regs.get? .misa = initial.regs.get? .misa ∧
    ∀ newer row older, rows = newer ++ row :: older →
      ∃ entry ∈ setup.program, ∃ rowBefore rowAfter,
        entry.SourceWith initial branchDecoderFields ∧ entry.SourceWith rowBefore branchDecoderFields ∧
        row.decoderQuery = entry.query ∧
        SailHistory cells (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
          initial rowBefore ∧
        SailHistory cells (rowEvents trace.memoryEpoch row).reverse rowBefore rowAfter ∧
        SailHistory cells (newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
          rowAfter after ∧ BranchRegisterTransfer row entry rowBefore rowAfter

end Airbender.ReducedMachine.Native
