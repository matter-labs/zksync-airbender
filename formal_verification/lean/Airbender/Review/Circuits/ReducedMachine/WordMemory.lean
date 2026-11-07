import Airbender.Review.Circuits.ReducedMachine.NativeArtifact

namespace Airbender.ReducedMachine.Native

/-- False is native word-only LW, true is native word-only SW. Original public
    decoding and memory/ROM semantics are separate connections. -/
def wordMemoryMask (store : Bool) : Nat := if store then 16386 else 1025

/-- Actual selected operand and port spaces only; no address/value answer. -/
structure WordMemoryRouting (w : Nat → ZMod mersenne31Modulus) (store : Bool) : Prop where
  operand : #v[w 47,w 48] = if store then #v[w 37,w 38] else #v[w 9,w 10]
  secondSpace : w 88 = if store then 1 else 0
  thirdSpace : w 89 = if store then 0 else 1

end Airbender.ReducedMachine.Native
