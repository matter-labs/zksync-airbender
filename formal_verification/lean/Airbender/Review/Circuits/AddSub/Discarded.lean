import Airbender.Review.Circuits.AddSub.Artifact
import Airbender.Review.Circuits.AddSub.Reference
import Airbender.Review.Helpers.Properties

/-!
Original pure instructions with destination x0 are preprocessed to a zero-operand
ADD/NOP row. This model retains their original Sail operand reads and PC
retirement. Loads discarded at x0 have separate memory and exception behavior;
they are outside this pure-instruction claim.
-/

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

/-- Physical low/high limb columns of one preprocessed word. -/
structure WordColumns where
  lo : Nat
  hi : Nat

/-- ADD is the first selector in the imported ADD/SUB selector interval. -/
structure SelectorColumns where
  add : Nat
  last : Nat

/-- Imported witness columns used by the discarded-destination adapter.
    PC columns retain the shared `PCMapping` interpretation. -/
structure RowColumns where
  execution : Nat
  destination : Nat
  left : WordColumns
  right : WordColumns
  immediate : WordColumns
  selectors : SelectorColumns

/-- Exact native column IDs; original Sail operands are not these zeroed words. -/
def nativeColumns : RowColumns where
  execution := 4
  destination := 7
  left := ⟨25, 26⟩
  right := ⟨29, 30⟩
  immediate := ⟨8, 9⟩
  selectors := ⟨10, 18⟩

/-- The native row participates in execution. -/
abbrev ExecutionSelected {p : Nat} (w : Nat → ZMod p) : Prop :=
  w nativeColumns.execution = 1

/-- The decoded destination is the architectural zero register. -/
abbrev DestinationIsZero {p : Nat} (w : Nat → ZMod p) : Prop :=
  w nativeColumns.destination = 0

/-- NOP preprocessing selects ADD and clears the other ADD/SUB selectors. -/
abbrev AddNopSelected {p : Nat} (w : Nat → ZMod p) : Prop :=
  ∀ k, nativeColumns.selectors.add ≤ k → k ≤ nativeColumns.selectors.last →
    w k = if k = nativeColumns.selectors.add then 1 else 0

/-- Both source words and the immediate are zero after preprocessing. -/
abbrev ZeroOperandPreprocessing {p : Nat} (w : Nat → ZMod p) : Prop :=
  w nativeColumns.left.lo = 0 ∧ w nativeColumns.left.hi = 0 ∧
  w nativeColumns.right.lo = 0 ∧ w nativeColumns.right.hi = 0 ∧
  w nativeColumns.immediate.lo = 0 ∧ w nativeColumns.immediate.hi = 0

/-- Bind the architectural PC transition and the native x0 destination. -/
abbrev RowMapping {p : Nat} (input : Input) (finalPC : Word) (w : Nat → ZMod p) : Prop :=
  PCMapping input.pc finalPC w ∧ DestinationIsZero w

/-- All pure x0 writes become NOP in `Instruction::pure_from_imm`; the ADD/SUB
    decoder selects zero-operand ADD. Only PC is an architectural output here. -/
def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Word (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := RowMapping

/-- Decoder/state obligations. Original operand reads must succeed even though
    preprocessing discarded their values. No operand bounds or result assumption. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (_finalPC : Word) (w : Nat → ZMod p) : Prop where
  active : ExecutionSelected w
  selection : AddNopSelected w
  preprocessing : ZeroOperandPreprocessing w
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
