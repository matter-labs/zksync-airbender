module
public import Human.Helpers.Decoder.RVPooledProgram

@[expose] public section

/-! External-input (CSR 0x7C0) decoder metadata: the native columns and selectors, projected from `RV.Instr` (`RV.decode`'s `inputRead`/`inputWrite`). -/

namespace Airbender.Trace.NonDeterminism

/-- The CSR 0x7C0 read (`csrrw rd, 0x7c0, x0`, rd ≠ x0) is an ADD/SUB
    row with selector 8 (mask 256) writing `rd`; the write (`csrrw x0, 0x7c0, rs1`) is preprocessed as the
    zero-operand ADD (NOP). Every other instruction uses the standard table. Sources: `add_sub_family/decoder.rs`,
    `riscv_transpiler/src/ir/simple_instruction_set.rs`. -/
def rvDecoderFields : RV.Instr → Option DecoderData
  | .inputRead rd => if rd = 0 then none else some ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩
  | .inputWrite _ => some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  | i => Trace.rvDecoderFields i

namespace Pooled

/-- The six-family registry extended with the CSR 0x7C0 forms. -/
def rvDecoderFields (i : RV.Instr) : Option (DecoderData PooledFamily) :=
  (NonDeterminism.rvDecoderFields i).map (DecoderData.mapFamily pooledArithmeticFamily) <|>
    rvPooledDecoderFields i

end Pooled
end Airbender.Trace.NonDeterminism
