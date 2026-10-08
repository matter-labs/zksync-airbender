import Airbender.Review.Trace.Program

namespace Airbender.Trace.NonDeterminism

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

end Airbender.Trace.NonDeterminism
