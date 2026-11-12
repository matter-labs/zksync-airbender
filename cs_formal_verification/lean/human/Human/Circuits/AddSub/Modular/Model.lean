module
public import Human.Circuits.AddSub.Artifact
public import Human.Helpers.Core.CircuitOutput
public import Human.Helpers.Core.Word
public import Human.ISA.RV32

@[expose] public section

namespace Airbender.AddSub.Modular
open Arithmetic

/-- The four field operations of the ADD/SUB circuit. -/
inductive Opcode where
  | add | sub | mul | fma
  deriving DecidableEq

/-- The imported selector column of each field operation. -/
def Opcode.selector : Opcode → Nat
  | .add => 13 | .sub => 14 | .mul => 15 | .fma => 16

/-- The corresponding instruction in the shared RV spec. -/
def Opcode.rvOp : Opcode → RV.FieldOp
  | .add => .add | .sub => .sub | .mul => .mul | .fma => .fma

/-- Original operand words and instruction fields, independent of the witness. -/
structure Input where
  /-- The selected field operation. -/
  opcode : Opcode
  /-- The first original operand. -/
  left : BitVec 32
  /-- The second original operand. -/
  right : BitVec 32
  /-- The destination value read by FMA. -/
  oldDestination : BitVec 32
  /-- The first source register. -/
  rs1 : RV.Reg
  /-- The second source register. -/
  rs2 : RV.Reg
  /-- The destination register. -/
  rd : RV.Reg
  /-- The mapped initial PC limbs. -/
  pc : Word
  /-- The row's RV pre-state. -/
  before : RV.State

/-- BabyBear arithmetic in Montgomery representation. The RV agreement proof fixes its meaning. -/
def arithmeticResult (opcode : Opcode) (left right oldDestination : BitVec 32) : ZMod babyBearModulus :=
  match opcode with
  | .add => (left.toNat : ZMod babyBearModulus) + right.toNat
  | .sub => (left.toNat : ZMod babyBearModulus) - right.toNat
  | .mul => (left.toNat : ZMod babyBearModulus) * right.toNat * (4294967296 : ZMod babyBearModulus)⁻¹
  | .fma => (left.toNat : ZMod babyBearModulus) * right.toNat * (4294967296 : ZMod babyBearModulus)⁻¹ +
      oldDestination.toNat

/-- Native whole-word residues. Discarded writes use ADD preprocessing. -/
structure WordMapping (input : Input) (output : Circuit.Output)
    (w : Nat → ZMod babyBearModulus) : Prop where
  /-- The native first operand is the original word's residue. -/
  left : input.rd ≠ 0 → w 25 + 65536 * w 26 = (input.left.toNat : ZMod babyBearModulus)
  /-- The native second operand is the original word's residue. -/
  right : input.rd ≠ 0 → w 29 + 65536 * w 30 = (input.right.toNat : ZMod babyBearModulus)
  /-- FMA reads the old destination before its write. -/
  oldDestination : input.rd ≠ 0 → input.opcode = .fma →
    w 31 + 65536 * w 32 = (input.oldDestination.toNat : ZMod babyBearModulus)
  /-- The native destination index is the architectural register number. -/
  destinationIndex : w 7 = (input.rd.toNat : ZMod babyBearModulus)
  /-- The initial low PC limb is mapped to its column. -/
  pcLo : w 0 = (input.pc.lo : ZMod babyBearModulus)
  /-- The initial high PC limb is mapped to its column. -/
  pcHi : w 1 = (input.pc.hi : ZMod babyBearModulus)
  /-- The output low limb is read from its column. -/
  outputLo : output.destination.lo = (w 33).val
  /-- The output high limb is read from its column. -/
  outputHi : output.destination.hi = (w 34).val
  /-- The final low PC limb is read from its column. -/
  finalPCLo : output.pc.lo = (w 19).val
  /-- The final high PC limb is read from its column. -/
  finalPCHi : output.pc.hi = (w 20).val

/-- Local selector and PC facts. Whole-machine execution must derive them from public decoding and history. -/
structure InterfaceAssumptions (input : Input) (_output : Circuit.Output)
    (w : Nat → ZMod babyBearModulus) : Prop where
  /-- The row participates. -/
  active : w 4 = 1
  /-- The decoded operation selects one field branch, or ADD for x0. -/
  selection : ∀ k, 10 ≤ k → k ≤ 18 →
    w k = if k = (if input.rd = 0 then 10 else input.opcode.selector) then 1 else 0
  /-- Both initial PC limbs are canonical. -/
  initialPCBounds : input.pc.Bounded

end Airbender.AddSub.Modular
