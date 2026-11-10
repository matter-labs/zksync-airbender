import Airbender.Review.Circuits.AddSub.Reference

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail

structure Contract (input : Input) : Prop where
  leftRead : input.row.opcode = .add ∨ input.row.opcode = .addi ∨ input.row.opcode = .sub →
    ∃ value, run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok value input.before ∧
      (input.rd ≠ zeroRegister → value = input.row.left.toBitVec)
  rightRead : input.row.opcode = .add ∨ input.row.opcode = .sub →
    ∃ value, run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok value input.before ∧
      (input.rd ≠ zeroRegister → value = input.row.right.toBitVec)
  signExtension : input.rd ≠ zeroRegister → input.row.opcode = .addi →
    input.row.immediate.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  upperImmediate : input.rd ≠ zeroRegister → input.row.opcode = .lui ∨ input.row.opcode = .auipc →
    input.row.immediate.toBitVec = SailRV32.Functions.sign_extend (m := 32)
      (input.encodedUpperImmediate ++ BitVec.ofNat 12 0)
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.row.pc.toBitVec input.before

end Airbender.Reference.RiscV.Sail
