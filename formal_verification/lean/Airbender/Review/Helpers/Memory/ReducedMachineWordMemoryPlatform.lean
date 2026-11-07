import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryTransfers
import Airbender.Review.Helpers.Memory.Platform

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option autoImplicit false

/-- Initial original reference configuration is required only when the public
    program contains a supported memory instruction. Empty programs stay CSR-free.
    This describes input CSRs/PMP/PMA/HTIF, not local success or physical enforcement. -/
def WordMemoryISA (setup : SparseDecoderSetup WordMemoryMode) (initial : State) : Prop :=
  setup.program ≠ [] → FlatMemoryConfiguration initial

/-- A public architectural RAM domain excluding the pinned platform's special
    CLINT/signature windows. Actual row addresses must first be rooted in cells. -/
def WordMemoryOrdinaryCells (cells : List Cell) : Prop :=
  ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address

/-- Reference dispatch only: retain the original LOAD/STORE clauses and operands. -/
def wordMemoryClause [MemoryPlatform SailRV32.exception] : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .LOAD (imm,rs1,rd,unsigned,width) => some (SailRV32.Functions.execute_LOAD imm rs1 rd unsigned width)
  | .STORE (imm,rs2,rs1,width) => some (SailRV32.Functions.execute_STORE imm rs2 rs1 width)
  | _ => none

/-- Successful retained original clauses at the actual constructed row states.
    PC preparation/retirement, fetched composition and mixed memory remain separate. -/
def WordMemoryClauseEffects [MemoryPlatform SailRV32.exception] (entry : WordMemoryProgramEntry) (before after : State) : Prop :=
  ∃ clause, wordMemoryClause entry.instruction = some clause ∧
    run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after

def WordMemoryClauseHistory [MemoryPlatform SailRV32.exception] (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup WordMemoryMode) (initial : State) (cells : List Cell) : Prop :=
  ∃ (history : TimestampSortedMemoryAccessList)
    (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : State),
    MemoryHistory trace history ∧ rows.Perm trace.rows ∧
    rows.Pairwise (fun a b => b.clock < a.clock) ∧
    SailHistory cells ((rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
      fun event => architecturalAddress event.2.1) initial after ∧
    SailStateMatches cells history after ∧
    (∀ key < 4194304, after.mem[key]? = initial.mem[key]?) ∧
    after.regs.get? .misa = initial.regs.get? .misa ∧
    ∀ newer row older, rows = newer ++ row :: older →
      ∃ entry ∈ setup.program, ∃ rowBefore rowAfter,
        entry.SourceWith initial wordMemoryDecoderFields ∧ entry.SourceWith rowBefore wordMemoryDecoderFields ∧
        row.decoderQuery = entry.query ∧
        SailHistory cells ((older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) initial rowBefore ∧
        SailHistory cells ((rowEvents trace.memoryEpoch row).reverse.filter
          fun event => architecturalAddress event.2.1) rowBefore rowAfter ∧
        SailHistory cells ((newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).filter
          fun event => architecturalAddress event.2.1) rowAfter after ∧
        WordMemoryNumericalEffects row.assignment entry ∧ WordMemoryTransfer row.assignment entry rowBefore rowAfter ∧
        WordMemoryClauseEffects entry rowBefore rowAfter

end Airbender.ReducedMachine.Native
