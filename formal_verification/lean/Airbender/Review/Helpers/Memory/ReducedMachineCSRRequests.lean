import Airbender.Review.Helpers.Memory.ReducedMachineCSR
import Airbender.Review.Circuits.ReducedMachine.RuntimeCSR

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail Reference.Sail Arithmetic
set_option autoImplicit false

/-- Reference observations for the explicitly selected runtime CSR configuration.
    Offset3 is imported in-cycle metadata, not an issuance or scheduling claim. -/
def csrRequestReference (index : Nat) (source : BitVec 32) : CSRRequest :=
  let delegated := NativeRuntimeCSR.delegated index
  ⟨(delegated : Nat),(index : ZMod mersenne31Modulus)*(delegated : Nat),
    some (((source.toNat/65536 : Nat) : ZMod mersenne31Modulus)*(delegated : Nat)),3⟩

/-- A derived original pre-state rs1 read identifies the actual canonical source
    word and imported request observations. No CSR clause or worker is executed. -/
def CSRSourceRequest (row : Row mersenne31Modulus NativeReducedFamily)
    (entry : CSRProgramEntry) (before : State) : Prop :=
  ∃ value : BitVec 32,
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before = .ok value before ∧
    value.toNat = (sourceWord row.assignment).value ∧
    sourceWord row.assignment = Word.ofBitVec value ∧
    csrRequest row.assignment = csrRequestReference entry.data.immediate.lo value

/-- The full chronological GPR realization, strengthened in the same segment
    states with original-source/request observations. This is not issuance,
    original CSR retirement, delegated RAM execution or worker fulfillment. -/
def CSRRequestHistory (trace : Data mersenne31Modulus NativeReducedFamily)
    (setup : SparseDecoderSetup CSRMode) (initial : State) (cells : List Cell) : Prop :=
  ∃ (history : TimestampSortedMemoryAccessList)
    (rows : List (Row mersenne31Modulus NativeReducedFamily)) (after : State),
    MemoryHistory trace history ∧ rows.Perm trace.rows ∧
    rows.Pairwise (fun a b => b.clock < a.clock) ∧
    SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
      initial after ∧ SailStateMatches cells history after ∧
    after.mem = initial.mem ∧ after.regs.get? .misa = initial.regs.get? .misa ∧
    ∀ newer row older, rows = newer ++ row :: older →
      ∃ entry ∈ setup.program, ∃ rowBefore rowAfter,
        entry.SourceWith initial csrDecoderFields ∧ entry.SourceWith rowBefore csrDecoderFields ∧
        row.decoderQuery = entry.query ∧
        SailHistory cells (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
          initial rowBefore ∧
        SailHistory cells (rowEvents trace.memoryEpoch row).reverse rowBefore rowAfter ∧
        SailHistory cells (newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse)
          rowAfter after ∧ CSRRegisterTransfer row entry rowBefore rowAfter ∧
        CSRSourceRequest row entry rowBefore

end Airbender.ReducedMachine.Native
