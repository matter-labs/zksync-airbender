import Airbender.Review.Circuits.AddSub.Artifact
import Airbender.Proofs.AddSub.SailContract
import Airbender.Review.Helpers.Properties

namespace Airbender.AddSub
open Reference.RiscV Arithmetic

/-- Public instruction interpreted in the native v2 packed family mask.
    V2 retains the original opcode for discarded x0 writes. -/
def decodedMask (input : Sail.Input) : Nat :=
  match input.row.opcode with
    | .add => 1 | .addi => 2 | .sub => 4 | .lui => 8 | .auipc => 16

/-- Preprocessed operands for nondiscarded writes; x0 needs no arithmetic interface. -/
abbrev Preprocessing (input : Sail.Input) : Prop :=
  if input.rd = Sail.zeroRegister then
    True
  else match input.row.opcode with
    | .add | .sub => input.row.immediate = ⟨0, 0⟩
    | .addi => input.row.right = ⟨0, 0⟩
    | .lui | .auipc => input.row.left = ⟨0, 0⟩ ∧ input.row.right = ⟨0, 0⟩

structure InputBounds (input : RowInput) : Prop where
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  immediateBound : input.immediate.Bounded

/-- Logical variable IDs resolved from the artifact's physical placement map.
    Destination observes the actual masked RAM/register write, not its raw hint. -/
structure RowWordMapping {p : Nat} (input : Sail.Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 25 = (input.row.left.lo : ZMod p)
  leftHi : w 26 = (input.row.left.hi : ZMod p)
  rightLo : w 27 = (input.row.right.lo : ZMod p)
  rightHi : w 28 = (input.row.right.hi : ZMod p)
  immediateLo : w 9 = (input.row.immediate.lo : ZMod p)
  immediateHi : w 10 = (input.row.immediate.hi : ZMod p)
  pcLo : w 0 = (input.row.pc.lo : ZMod p)
  pcHi : w 1 = (input.row.pc.hi : ZMod p)
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 37).val
  outputHi : output.destination.hi = (w 38).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Sail.Input Sail.Output (Nat → ZMod p) where
  satisfies w := FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := RowWordMapping

/-- Local row milestone. Native public decoding, initialized history and setup
    extraction must discharge these interfaces before claiming whole execution. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Sail.Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  /-- Native preprocessed decoder mask; individual selector bits are derived. -/
  decoderMask : w 12 = (decodedMask input : ZMod p)
  destinationZero : w 8 = if input.rd = Sail.zeroRegister then 1 else 0
  preprocessing : Preprocessing input
  operands : input.rd ≠ Sail.zeroRegister → InputBounds input.row
  initialPCBounds : input.row.pc.Bounded
  /-- The v2 low-PC carry detector is for four-byte aligned instructions. -/
  initialPCAligned : input.row.pc.lo % 4 = 0
  /-- Actual upstream reads and immediate encoding, not expected results. -/
  registers : Sail.Contract input

end Airbender.AddSub
