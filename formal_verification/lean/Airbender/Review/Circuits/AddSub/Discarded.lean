import Airbender.Review.Circuits.AddSub.Artifact
import Airbender.Review.Circuits.AddSub.Reference
import Airbender.Review.Helpers.Properties

namespace Airbender.AddSub.Discarded
open Airbender.Arithmetic
open Airbender.Reference.RiscV

/-- Original pure instructions writing x0. These select native Sail clauses,
    not a replacement arithmetic specification. -/
inductive Instruction where
  | register (op : SailRV32.rop) (rs1 rs2 : SailRV32.regidx)
  | immediate (op : SailRV32.iop) (rs1 : SailRV32.regidx) (imm : BitVec 12)
  | shiftImmediate (op : SailRV32.sop) (rs1 : SailRV32.regidx) (amount : BitVec 6)
  | rev8 (rs1 : SailRV32.regidx)
  | multiply (op : SailRV32.mul_op) (rs1 rs2 : SailRV32.regidx)
  | divide (unsigned : Bool) (rs1 rs2 : SailRV32.regidx)
  | remainder (unsigned : Bool) (rs1 rs2 : SailRV32.regidx)

structure Input where
  instruction : Instruction
  pc : Word
  before : Sail.State

def execution (instruction : Instruction) : SailRV32.SailM SailRV32.ExecutionResult :=
  match instruction with
  | .register op rs1 rs2 => SailRV32.Functions.execute_RTYPE rs2 rs1 Sail.zeroRegister op
  | .immediate op rs1 imm => SailRV32.Functions.execute_ITYPE imm rs1 Sail.zeroRegister op
  | .shiftImmediate op rs1 amount => SailRV32.Functions.execute_SHIFTIOP amount rs1 Sail.zeroRegister op
  | .rev8 rs1 => SailRV32.Functions.execute_REV8 rs1 Sail.zeroRegister
  | .multiply op rs1 rs2 => SailRV32.Functions.execute_MUL rs2 rs1 Sail.zeroRegister op
  | .divide unsigned rs1 rs2 => SailRV32.Functions.execute_DIV rs2 rs1 Sail.zeroRegister unsigned
  | .remainder unsigned rs1 rs2 => SailRV32.Functions.execute_REM rs2 rs1 Sail.zeroRegister unsigned

abbrev spec (input : Input) (finalPC : Word) : Prop :=
  Sail.stepSpec input.before (execution input.instruction) Sail.zeroRegister ⟨⟨0, 0⟩, finalPC⟩

/-- All pure x0 writes become NOP in `Instruction::pure_from_imm`; the ADD/SUB
    decoder selects zero-operand ADD. Only PC is an architectural output here. -/
def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Word (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input finalPC w => PCMapping input.pc finalPC w ∧ w 7 = 0

/-- Decoder/state obligations. Original operand reads must succeed even though
    preprocessing discarded their values. No operand bounds or result assumption. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (_finalPC : Word) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selection : ∀ k, 10 ≤ k → k ≤ 18 → w k = if k = 10 then 1 else 0
  preprocessing : w 25 = 0 ∧ w 26 = 0 ∧ w 29 = 0 ∧ w 30 = 0 ∧ w 8 = 0 ∧ w 9 = 0
  initialPCBounds : input.pc.Bounded
  reads : match input.instruction with
    | .register _ rs1 rs2 | .multiply _ rs1 rs2 | .divide _ rs1 rs2 | .remainder _ rs1 rs2 => ∃ left right,
        Reference.Sail.run (SailRV32.Functions.rX_bits rs1) input.before = .ok left input.before ∧
        Reference.Sail.run (SailRV32.Functions.rX_bits rs2) input.before = .ok right input.before
    | .immediate _ rs1 _ | .shiftImmediate _ rs1 _ | .rev8 rs1 => ∃ left,
        Reference.Sail.run (SailRV32.Functions.rX_bits rs1) input.before = .ok left input.before
  pcRead : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before

end Airbender.AddSub.Discarded
