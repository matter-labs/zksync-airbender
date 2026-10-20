import Human.Circuits.ShiftBinop.Model

namespace Airbender.ShiftBinop
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail

/-- Binary queries combine rs2 bytes with the packed immediate/sign byte.
    Shift queries use rs2 truncation plus the immediate's low five bits; REV8 uses zero.
    These mappings identify operands; none prescribes the result. -/
structure RowWordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftBytes : ∀ i : Fin 4,
    w (19 + i.val) = ((input.left.extractLsb' (8 * i.val) 8).toNat : ZMod p)
  binaryRightBytes : input.operation.isShift = false → ∀ i : Fin 4,
    w (25 + i.val) +
      (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((BitVec.extractLsb' (8 * i.val) 8
        input.right).toNat : ZMod p)
  shiftLowByte : input.operation.isShift = true →
    w 25 = ((BitVec.extractLsb' 0 8
      (if input.immediate || input.operation = .rev8 then 0 else input.right)).toNat : ZMod p)
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

def rowCircuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => RowWordMapping input output w

/-- Decoder selection and successful native reads remain interfaces. Native word
    mappings and lookups provide byte bounds; no operand ranges are assumed. -/
structure RowInterfaces {p : Nat} [Fact p.Prime] (input : Input)
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
