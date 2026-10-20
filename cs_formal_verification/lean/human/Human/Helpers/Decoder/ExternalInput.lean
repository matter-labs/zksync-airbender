import Human.Helpers.Context.Boundary
import Human.Helpers.Decoder.Instruction
import Human.Helpers.Core.ExternalStream

namespace Airbender.Trace.NonDeterminism

variable {p : Nat} [Fact p.Prime]

/-- Extend native metadata projection with the pinned project's CSRRW 0x7C0
    operations. The actual instruction still comes from Sail's decoder.
    Read: rs1=x0 and rd≠x0, selector 8. Write: rs1≠x0 and rd=x0,
    preprocessed as zero-operand ADD/NOP. Unsupported CSR forms fail.
    Sources: `docs/airbender/00-master.md`, `add_sub_family/decoder.rs`,
    `riscv_transpiler/src/ir/simple_instruction_set.rs`. This is metadata,
    not Sail's standard CSR execution or an application I/O specification. -/
def decoderFields (instruction : SailRV32.instruction) : Option DecoderData :=
  match instruction with
  | .CSRReg (csr, .Regidx rs1, .Regidx rd, .CSRRW) =>
    if csr = 0x7C0 then
      if rs1 = 0 then
        if rd = 0 then none
        else some ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩
      else if rd = 0 then some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
      else none
    else none
  | _ => Trace.decoderFields instruction

/-- The pinned project's external-read form. Sail supplies this instruction
    constructor from public bytes; the decoder proof ties it to selector 8. -/
def instructionRead : SailRV32.instruction → Bool
  | .CSRReg (csr, .Regidx rs1, .Regidx rd, .CSRRW) =>
    decide (csr = 0x7C0 ∧ rs1 = 0 ∧ rd ≠ 0)
  | _ => false

/-- Native selector 8 identifies external reads. Word-memory rows never consume
    this stream; actual CSR correspondence is checked by decoder soundness. -/
def isRead (row : Row p) : Bool :=
  match row.family with
  | .addSub => row.assignment 18 == 1
  | .wordMemory => false

/-- The word exposed by a native external-read row's destination columns.
    `StreamPorts` binds it to an independently supplied external stream. -/
def response (row : Row p) : BitVec 32 :=
  (Arithmetic.Word.mk (row.assignment 33).val (row.assignment 34).val).toBitVec

/-- Count earlier reads by native clock, never by witness-list position. -/
def readIndex (trace : Data p) (row : Row p) : Nat :=
  ExternalStream.index Row.clock isRead trace.rows row

/-- Number of external-read rows; standard instructions and write/hint rows
    consume no words. Soundness proves the final stream position equals this count. -/
def readCount (trace : Data p) : Nat := ExternalStream.count isRead trace.rows

/-- Bind each external-read row to `stream` at its clock-ordered read index.
    The caller supplies this stream independently of the witness. This is an
    explicit external-input boundary: native constraints permit nondeterminism
    and do not authenticate which external stream was chosen. -/
def StreamPorts (trace : Data p) (stream : List (BitVec 32)) : Prop :=
  ExternalStream.Ports Row.clock isRead response trace.rows stream

/-- Responses in execution order. Native history lists use descending clocks,
    hence the reversal; writes/hints and standard instructions consume nothing. -/
def consumed (rows : List (Row p)) : List (BitVec 32) :=
  ExternalStream.consumed isRead response rows

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The pinned project's custom CSR operations, using native Sail effects.
    A read writes the next external word; a write is an architectural no-op
    (simulator hints are outside the claim). `profile` selects standard-instruction
    semantics: unchanged Sail, or the explicit Airbender discarded-LW rule. -/
def clause (stream : List (BitVec 32)) (position : Nat) (instruction : SailRV32.instruction)
    (profile : ISAProfile := .airbender) :
    Option (SailRV32.SailM SailRV32.ExecutionResult × Nat) :=
  match instruction with
  | .CSRReg (csr, .Regidx rs1, .Regidx rd, .CSRRW) =>
    if csr = 0x7C0 then
      if rs1 = 0 then
        if rd = 0 then none else do
          let value ← stream[position]?
          pure (Reference.RiscV.Sail.writeResult (.Regidx rd) (Arithmetic.Word.ofBitVec value), position + 1)
      else if rd = 0 then some (pure SailRV32.Functions.RETIRE_SUCCESS, position)
      else none
    else none
  | _ => (profileClause profile instruction).map fun original => (original, position)

end Airbender.Trace.NonDeterminism
