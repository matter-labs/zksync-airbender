import Airbender.Review.Circuits.ReducedMachine.NativeArtifact
import Airbender.Review.Helpers.Core.Word

namespace Airbender.ReducedMachine.Native

/-- False is native word-only LW, true is native word-only SW. Original public
    decoding and memory/ROM semantics are separate connections. -/
def wordMemoryMask (store : Bool) : Nat := if store then 16386 else 1025

/-- Actual selected operand and port spaces only; no address/value answer. -/
structure WordMemoryRouting (w : Nat → ZMod mersenne31Modulus) (store : Bool) : Prop where
  operand : #v[w 47,w 48] = if store then #v[w 37,w 38] else #v[w 9,w 10]
  secondSpace : w 88 = if store then 1 else 0
  thirdSpace : w 89 = if store then 0 else 1

/-- Actual shared native effective-address and decoded-immediate columns. -/
def wordMemoryAddressWord (w : Nat → ZMod mersenne31Modulus) : Arithmetic.Word :=
  ⟨(w 61).val,(w 62).val⟩

def wordMemoryImmediateWord (w : Nat → ZMod mersenne31Modulus) : Arithmetic.Word :=
  ⟨(w 9).val,(w 10).val⟩

/-- Actual load ports and selection. The ROM words and RAM predicate still need
    their exact fixed-table meanings; original memory observations are separate. -/
structure WordLoadAccess (w : Nat → ZMod mersenne31Modulus) : Prop where
  shadowAddress : #v[w 39,w 40] = #v[w 61,w 62]
  romSelector : w 86 = 1-w 64
  ramSelector : w 87 = w 64
  candidate : #v[w 116,w 117] =
    #v[(1-w 64)*w 66+w 64*w 37,(1-w 64)*w 67+w 64*w 38]
  destination : #v[w 45,w 46] = #v[w 7,0]
  written : #v[w 43,w 44] = #v[(1-w 8)*w 116,(1-w 8)*w 117]

/-- The store port writes memory directly from its retained second source.
    Architectural destination masking has no role in this write. -/
structure WordStoreAccess (w : Nat → ZMod mersenne31Modulus) : Prop where
  sourceAddress : #v[w 39,w 40] = #v[w 6,0]
  destination : #v[w 45,w 46] = #v[w 61,w 62]
  written : #v[w 43,w 44] = #v[w 37,w 38]
  offsetSum : w 64+w 65 = 0
  ram : w 66 = 1

end Airbender.ReducedMachine.Native
