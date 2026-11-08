module
public import Human.Circuits.AddSub.Artifact
public import Human.Helpers.Properties
public import Human.Helpers.Core.Field
public import Human.Helpers.Core.CircuitOutput

@[expose] public section

namespace Airbender.AddSub.Modular
open Airbender.Arithmetic

inductive Opcode where
  | add | sub | mul | fma
  deriving DecidableEq

def Opcode.selector : Opcode → Nat
  | .add => 13 | .sub => 14 | .mul => 15 | .fma => 16

/-- Custom arithmetic from docs/airbender/00-master.md. This is a reviewed project
    specification, not an upstream Sail instruction. Montgomery radix is 2^32. -/
def arithmeticResult (opcode : Opcode) (left right oldDestination : BitVec 32) : ZMod babyBearModulus :=
  match opcode with
  | .add => (left.toNat : ZMod babyBearModulus) + right.toNat
  | .sub => (left.toNat : ZMod babyBearModulus) - right.toNat
  | .mul => (left.toNat : ZMod babyBearModulus) * right.toNat * (4294967296 : ZMod babyBearModulus)⁻¹
  | .fma => (left.toNat : ZMod babyBearModulus) * right.toNat * (4294967296 : ZMod babyBearModulus)⁻¹ +
      oldDestination.toNat

end Airbender.AddSub.Modular
