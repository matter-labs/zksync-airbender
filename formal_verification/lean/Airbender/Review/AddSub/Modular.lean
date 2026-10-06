import Airbender.Review.AddSub.Artifact
import Airbender.Review.Properties
import Airbender.Review.Word
import Airbender.Review.Field

namespace Airbender.AddSub.Modular
open Airbender.Arithmetic

inductive Opcode where
  | add | sub | mul | fma
  deriving DecidableEq

def Opcode.selector : Opcode → Nat
  | .add => 13 | .sub => 14 | .mul => 15 | .fma => 16

/-- Word-level custom operands. Binding these to architectural registers is a
    later interface obligation; this claim does not include register or PC effects. -/
structure Input where
  opcode : Opcode
  left : BitVec 32
  right : BitVec 32
  oldDestination : BitVec 32

/-- ADDMOD/SUBMOD/MULMOD/FMAMOD from the pinned project specification,
    vendor/airbender/00-master.md. Multiplication uses Montgomery radix 2^32. -/
def spec (input : Input) (output : Word) : Prop :=
  output.value = (match input.opcode with
    | .add => (input.left.toNat : ZMod babyBearModulus) + input.right.toNat
    | .sub => (input.left.toNat : ZMod babyBearModulus) - input.right.toNat
    | .mul => (input.left.toNat : ZMod babyBearModulus) * input.right.toNat *
        (4294967296 : ZMod babyBearModulus)⁻¹
    | .fma => (input.left.toNat : ZMod babyBearModulus) * input.right.toNat *
        (4294967296 : ZMod babyBearModulus)⁻¹ + input.oldDestination.toNat).val

/-- Whole-word residues suffice for these modular operations; no desired output
    or canonical-output bound is assumed. -/
structure WordMapping (input : Input) (output : Word)
    (w : Nat → ZMod babyBearModulus) : Prop where
  left : w 25 + 65536 * w 26 = (input.left.toNat : ZMod babyBearModulus)
  right : w 29 + 65536 * w 30 = (input.right.toNat : ZMod babyBearModulus)
  oldDestination : input.opcode = .fma →
    w 31 + 65536 * w 32 = (input.oldDestination.toNat : ZMod babyBearModulus)
  outputLo : output.lo = (w 33).val
  outputHi : output.hi = (w 34).val

def circuitModel [Fact babyBearModulus.Prime] :
    Verification.CircuitModel Input Word (Nat → ZMod babyBearModulus) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder interface: a single modular selector on an active row. -/
structure InterfaceAssumptions (input : Input) (_output : Word)
    (w : Nat → ZMod babyBearModulus) : Prop where
  active : w 4 = 1
  selection : ∀ k, 10 ≤ k → k ≤ 18 → w k = if k = input.opcode.selector then 1 else 0

end Airbender.AddSub.Modular
