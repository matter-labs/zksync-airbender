import Airbender.Review.Circuits.AddSub.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Review.Helpers.Sail
import Airbender.Review.Helpers.Field

namespace Airbender.AddSub.Modular
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

inductive Opcode where
  | add | sub | mul | fma
  deriving DecidableEq

def Opcode.selector : Opcode → Nat
  | .add => 13 | .sub => 14 | .mul => 15 | .fma => 16

/-- Original register operands and fixed native state, independent of the circuit witness. -/
structure Input where
  opcode : Opcode
  left : BitVec 32
  right : BitVec 32
  oldDestination : BitVec 32
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  pc : Word
  before : Sail.State

/-- Custom arithmetic from vendor/airbender/00-master.md. This is a reviewed project
    specification, not an upstream Sail instruction. Montgomery radix is 2^32. -/
def arithmeticResult (opcode : Opcode) (left right oldDestination : BitVec 32) : ZMod babyBearModulus :=
  match opcode with
  | .add => (left.toNat : ZMod babyBearModulus) + right.toNat
  | .sub => (left.toNat : ZMod babyBearModulus) - right.toNat
  | .mul => (left.toNat : ZMod babyBearModulus) * right.toNat * (4294967296 : ZMod babyBearModulus)⁻¹
  | .fma => (left.toNat : ZMod babyBearModulus) * right.toNat * (4294967296 : ZMod babyBearModulus)⁻¹ +
      oldDestination.toNat

/-- Read all original operands before writing. Reuse native Sail register effects,
    including discarded x0 writes; only custom arithmetic is defined locally. -/
def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult := do
  let left ← SailRV32.Functions.rX_bits input.rs1
  let right ← SailRV32.Functions.rX_bits input.rs2
  let old ← match input.opcode with
    | .fma => SailRV32.Functions.rX_bits input.rd
    | _ => pure 0
  SailRV32.Functions.wX_bits input.rd (BitVec.ofNat 32 (arithmeticResult input.opcode left right old).val)
  pure SailRV32.Functions.RETIRE_SUCCESS

/-- Same architectural claim as standard branches, using the reviewed custom execution. -/
abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Whole-word residues suffice for custom arithmetic. x0 preprocessing removes
    operand agreement, while the initial PC and destination index remain mapped. -/
structure WordMapping (input : Input) (output : Sail.Output)
    (w : Nat → ZMod babyBearModulus) : Prop where
  left : input.rd ≠ Sail.zeroRegister →
    w 25 + 65536 * w 26 = (input.left.toNat : ZMod babyBearModulus)
  right : input.rd ≠ Sail.zeroRegister →
    w 29 + 65536 * w 30 = (input.right.toNat : ZMod babyBearModulus)
  oldDestination : input.rd ≠ Sail.zeroRegister → input.opcode = .fma →
    w 31 + 65536 * w 32 = (input.oldDestination.toNat : ZMod babyBearModulus)
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod babyBearModulus)
  pcLo : w 0 = (input.pc.lo : ZMod babyBearModulus)
  pcHi : w 1 = (input.pc.hi : ZMod babyBearModulus)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 19).val
  finalPCHi : output.pc.hi = (w 20).val

def circuitModel [Fact babyBearModulus.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod babyBearModulus) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Successful native reads. Only non-discarded results require value agreement;
    FMA additionally reads the old destination before any write. -/
structure RegisterContract (input : Input) : Prop where
  leftRead : ∃ value, run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok value input.before ∧
    (input.rd ≠ Sail.zeroRegister → value = input.left)
  rightRead : ∃ value, run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok value input.before ∧
    (input.rd ≠ Sail.zeroRegister → value = input.right)
  oldRead : input.rd ≠ Sail.zeroRegister → input.opcode = .fma →
    run (SailRV32.Functions.rX_bits input.rd) input.before = .ok input.oldDestination input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before

/-- Decoder/memory interfaces. A discarded custom write is preprocessed into ADD. -/
structure InterfaceAssumptions (input : Input) (_output : Sail.Output)
    (w : Nat → ZMod babyBearModulus) : Prop where
  active : w 4 = 1
  selection : ∀ k, 10 ≤ k → k ≤ 18 →
    w k = if k = (if input.rd = Sail.zeroRegister then 10 else input.opcode.selector) then 1 else 0
  initialPCBounds : input.pc.Bounded
  registers : RegisterContract input

end Airbender.AddSub.Modular
