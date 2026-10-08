import Airbender.Review.Trace.Execution

namespace Airbender.Trace.NonDeterminism

variable {p : Nat} [Fact p.Prime]

/-- Extend native metadata projection with the pinned project's CSRRW 0x7C0
    operations. The actual instruction still comes from Sail's decoder.
    Read: rs1=x0 and rd≠x0, selector 8. Write: rs1≠x0 and rd=x0,
    preprocessed as zero-operand ADD/NOP. Unsupported CSR forms fail.
    Sources: `vendor/airbender/00-master.md`, `add_sub_family/decoder.rs`,
    `riscv_transpiler/src/ir/simple_instruction_set.rs`. This is metadata,
    not Sail's standard CSR execution or an application I/O specification. -/
def decoderFields (instruction : SailRV32.instruction) : Option DecoderData :=
  match instruction with
  | .CSRReg (csr, .Regidx rs1, .Regidx rd, .CSRRW) =>
    if csr = 0x7C0 then
      if rs1 = 0 then
        if rd = 0 then none
        else some ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256⟩
      else if rd = 0 then some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1⟩
      else none
    else none
  | _ => Trace.decoderFields instruction

/-- Native selector 8 identifies external reads. Word-memory rows never consume
    this stream; actual CSR correspondence is checked by decoder soundness. -/
def isRead (row : Row p) : Bool :=
  match row.family with
  | .addSub => row.assignment 18 == 1
  | .wordMemory => false

def response (row : Row p) : BitVec 32 :=
  (Arithmetic.Word.mk (row.assignment 33).val (row.assignment 34).val).toBitVec

/-- Count earlier reads by native clock, never by witness-list position. -/
def readIndex (trace : Data p) (row : Row p) : Nat :=
  (trace.rows.filter fun earlier => isRead earlier && decide (earlier.clock < row.clock)).length

/-- The explicit external-input connection. The stream is supplied independently
    of the witness; the circuit itself does not authenticate a fixed stream. -/
def StreamPorts (trace : Data p) (stream : List (BitVec 32)) : Prop :=
  ∀ row ∈ trace.rows, isRead row = true →
    stream[readIndex trace row]? = some (response row)

/-- Responses in execution order. Native history lists use descending clocks,
    hence the reversal; writes/hints and standard instructions consume nothing. -/
def consumed (rows : List (Row p)) : List (BitVec 32) :=
  rows.reverse.filterMap fun row => if isRead row then some (response row) else none

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The pinned project's custom CSR operations, using native Sail effects.
    A read writes the next external word; a write is an architectural no-op
    (simulator hints are outside the claim). Standard instructions retain the
    existing Airbender profile, including its explicit discarded-LW rule. -/
def clause (stream : List (BitVec 32)) (position : Nat) (instruction : SailRV32.instruction) :
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
  | _ => (profileClause .airbender instruction).map fun original => (original, position)

/-- State is Sail's state plus the external-stream position. Fetch and decode
    use the actual public bytes; custom behavior is visible in `clause` above. -/
def Step (stream : List (BitVec 32)) (program : List ProgramEntry)
    (before after : Reference.RiscV.Sail.State × Nat) : Prop :=
  ∃ entry ∈ program, entry.Source before.1 decoderFields ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before.1 = .ok entry.pc before.1 ∧
    ∃ original, clause stream before.2 entry.instruction = some (original, after.2) ∧
      Reference.Sail.run (Reference.RiscV.Sail.normalStep original) before.1 =
        .ok SailRV32.Functions.RETIRE_SUCCESS after.1

abbrev ExecutionTrace (stream : List (BitVec 32)) (program : List ProgramEntry) :=
  Relation.ReflTransGen (Step stream program)

end Airbender.Trace.NonDeterminism
