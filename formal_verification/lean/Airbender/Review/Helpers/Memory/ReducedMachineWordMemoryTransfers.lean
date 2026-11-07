import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryHistory
import Airbender.Review.Circuits.ReducedMachine.WordMemoryResult

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail Reference.Sail
set_option autoImplicit false

/-- Original same-pre-state GPR/byte-memory transfers for actual native LW/SW.
    ROM reads are architectural bytes; ignored shadow values stay independent.
    LOAD-to-x0 reads its unmasked value before the original x0 accessor discards
    the write. STORE writes RAM regardless of its decoded dummy rd. -/
structure WordMemoryTransfer (w : Nat → ZMod mersenne31Modulus) (entry : WordMemoryProgramEntry)
    (before after : State) : Prop where
  retainedReads : ∀ i : Fin 3, (wordMemoryPortDomains w entry)[i] = true →
    (wordMemoryPortCells w entry)[i].read before =
      .ok (memoryWord (importedConstraintsMemoryPorts[i].readCode w)) before
  sourceRead : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
    .ok (sourceWord w).toBitVec before
  nativeWrite : run ((wordMemoryPortCells w entry)[2].write (wordMemoryWrittenWord w).toBitVec) before =
    .ok () after
  load : entry.data.family = false →
    (Cell.ram (wordMemoryAddressWord w).toBitVec).read before = .ok (wordMemoryLoadWord w).toBitVec before ∧
      run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) (wordMemoryLoadWord w).toBitVec) before = .ok () after
  store : entry.data.family = true →
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before = .ok (wordMemorySecondWord w).toBitVec before ∧
      run (writeMemory (size := 4) (wordMemoryAddressWord w).toBitVec (wordMemorySecondWord w).toBitVec)
        before = .ok () after

/-- Initialized native matching constructs all states and transfers; no per-row
    read/write/range/address/result/state answer is supplied. Retained original
    virtual-memory checks, clauses and normal/fetched execution remain separate. -/
def WordMemoryTransferHistory (trace : Data mersenne31Modulus NativeReducedFamily)
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
        WordMemoryNumericalEffects row.assignment entry ∧ WordMemoryTransfer row.assignment entry rowBefore rowAfter

end Airbender.ReducedMachine.Native
