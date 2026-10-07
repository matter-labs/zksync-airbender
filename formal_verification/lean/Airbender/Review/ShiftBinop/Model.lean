import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail

namespace Airbender.ShiftBinop
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

inductive Operation where
  | xor | or | and | sll | srl | sra | rev8
  deriving DecidableEq

def Operation.tag : Operation → Nat
  | .xor => 4 | .or => 6 | .and => 7
  | .sll => 1 | .srl => 2 | .sra => 3 | .rev8 => 5

def Operation.isShift : Operation → Bool
  | .sll | .srl | .sra | .rev8 => true
  | _ => false

/-- Native source words; binary immediates use `right` after Sail sign extension.
    Immediate shifts use the encoded payload. Source and destination may alias. -/
structure Input where
  operation : Operation
  immediate : Bool
  left : BitVec 32
  right : BitVec 32
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  match input.operation, input.immediate with
  | .rev8, _ => SailRV32.Functions.execute_REV8 input.rs1 input.rd
  | .xor, true => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .XORI
  | .or, true => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .ORI
  | .and, true => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .ANDI
  | .sll, true => SailRV32.Functions.execute_SHIFTIOP (input.encodedImmediate.extractLsb' 0 6) input.rs1 input.rd .SLLI
  | .srl, true => SailRV32.Functions.execute_SHIFTIOP (input.encodedImmediate.extractLsb' 0 6) input.rs1 input.rd .SRLI
  | .sra, true => SailRV32.Functions.execute_SHIFTIOP (input.encodedImmediate.extractLsb' 0 6) input.rs1 input.rd .SRAI
  | .xor, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .XOR
  | .or, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .OR
  | .and, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .AND
  | .sll, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SLL
  | .srl, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SRL
  | .sra, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SRA

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Binary queries combine rs2 bytes with the packed immediate/sign byte.
    Shift queries use rs2 truncation plus the immediate's low five bits; REV8 uses zero.
    These mappings identify operands; none prescribes the result. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftBytes : ∀ i : Fin 4,
    w (19 + i.val) = ((input.left.extractLsb' (8 * i.val) 8).toNat : ZMod p)
  rightBytes : ∀ i : Fin 4,
    w (25 + i.val) + (if input.operation.isShift then 0 else
      if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((BitVec.extractLsb' (8 * i.val) 8
        (if input.operation.isShift && input.immediate || input.operation = .rev8 then 0 else input.right)).toNat : ZMod p)
  shiftImmediate : input.operation.isShift = true →
    w 8 = (if input.operation = .rev8 then 0 else if input.immediate then (input.encodedImmediate.extractLsb' 0 5).toNat else 0 : ZMod p)
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : w 0 = (input.pc.lo : ZMod p)
  pcHi : w 1 = (input.pc.hi : ZMod p)
  outputLo : output.destination.lo = (w 31).val
  outputHi : output.destination.hi = (w 32).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder selection and successful native reads remain interfaces. Native word
    mappings and lookups provide byte bounds; no operand ranges are assumed. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : if input.operation.isShift then w 11 = 1 ∧ w 12 = 0 else w 11 = 0 ∧ w 12 = 1
  funct3 : w 10 = (input.operation.tag : ZMod p)
  nonzeroDestination : input.rd ≠ Sail.zeroRegister
  initialPCBound : input.pc.Bounded
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left input.before
  rightRead : input.immediate = false → input.operation ≠ .rev8 →
    run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before
  signExtension : input.immediate = true → input.operation.isShift = false →
    input.right = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  shiftEncoding : input.immediate = true → input.operation.isShift = true → input.operation ≠ .rev8 →
    (input.encodedImmediate.extractLsb' 0 6).toNat < 32
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before

end Airbender.ShiftBinop
