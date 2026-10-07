import Airbender.Review.UnifiedReduced.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail

namespace Airbender.UnifiedReduced.TriAdd
open Airbender.Reference.RiscV
open Airbender.Reference.Sail
open Airbender.Arithmetic

structure Input where
  left : Word
  right : Word
  oldDestination : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  pc : Word
  before : Sail.State

/-- MOP.RR.4 from vendor/airbender/00-master.md: rd_old + rs1 + rs2 modulo
    2^32. This is a project operation, using Sail's native register effects. -/
def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult := do
  let left ← SailRV32.Functions.rX_bits input.rs1
  let right ← SailRV32.Functions.rX_bits input.rs2
  let old ← SailRV32.Functions.rX_bits input.rd
  SailRV32.Functions.wX_bits input.rd (old + left + right)
  pure SailRV32.Functions.RETIRE_SUCCESS

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  operands : input.rd ≠ Sail.zeroRegister →
    w 36 = (input.left.lo : ZMod p) ∧ w 37 = (input.left.hi : ZMod p) ∧
    w 42 = (input.right.lo : ZMod p) ∧ w 43 = (input.right.hi : ZMod p) ∧
    w 48 = (input.oldDestination.lo : ZMod p) ∧ w 49 = (input.oldDestination.hi : ZMod p)
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : w 0 = (input.pc.lo : ZMod p)
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.destination.lo = (w 50).val
  outputHi : output.destination.hi = (w 51).val
  finalPCLo : output.pc.lo = (w 30).val
  finalPCHi : output.pc.hi = (w 31).val

def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)
  represents := fun input output w => WordMapping input output w

/-- All original reads must succeed. Discarded x0 writes need no operand agreement. -/
structure RegisterContract (input : Input) : Prop where
  leftRead : ∃ value, run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok value input.before ∧
    (input.rd ≠ Sail.zeroRegister → value = input.left.toBitVec)
  rightRead : ∃ value, run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok value input.before ∧
    (input.rd ≠ Sail.zeroRegister → value = input.right.toBitVec)
  oldRead : ∃ value, run (SailRV32.Functions.rX_bits input.rd) input.before = .ok value input.before ∧
    (input.rd ≠ Sail.zeroRegister → value = input.oldDestination.toBitVec)
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before

structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : w Variables.dispatchColumns[(if input.rd = Sail.zeroRegister then 0 else 9 : Fin 18)] = 1
  ranges : input.rd ≠ Sail.zeroRegister → input.left.Bounded ∧ input.right.Bounded ∧ input.oldDestination.Bounded
  initialPCLoBound : input.pc.lo < limbBase
  registers : RegisterContract input

end Airbender.UnifiedReduced.TriAdd
