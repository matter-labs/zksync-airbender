import Airbender.Review.Circuits.SubwordMemory.Artifact
import Airbender.Proofs.Mersenne31
import Airbender.Review.Helpers.Tables.SubwordLoad
import Airbender.Review.Helpers.Tables.SubwordStoreClear
import Airbender.Review.Helpers.Tables.SubwordStorePlace
import Airbender.Review.Helpers.Tables.AlignedWordROM

namespace Airbender.SubwordMemory
open Verification
set_option autoImplicit false

/-- Native selector and the two observed memory limbs. -/
def selectedLimb (w : Nat → ZMod mersenne31Modulus) (low high : Nat) : ZMod mersenne31Modulus :=
  (1 - w 25) * w low + w 25 * w high

/-- The native table key retains the offset and raw funct3 encoding. -/
def dataKey (w : Nat → ZMod mersenne31Modulus) (limb : ZMod mersenne31Modulus) : ZMod mersenne31Modulus :=
  limb + 65536 * w 22 + 262144 * w 11

/-- V2's aligned ROM uses a word index and the native field inverse of four. -/
def romWordKey (w : Nat → ZMod mersenne31Modulus) : ZMod mersenne31Modulus :=
  536870912 * (w 19 - w 22 + 65536 * w 27)

/-- Exhaustive accepted modes, with tags derived from native equations. -/
def ModeRouting (w : Nat → ZMod mersenne31Modulus) : Prop :=
  (w 12 = 0 ∧ (w 20).val < 64 ∧ w 55 = 46 ∧ w 59 = 45) ∨
  (w 12 = 0 ∧ 64 ≤ (w 20).val ∧ w 55 = 45 ∧ w 59 = 0) ∨
  (w 12 = 1 ∧ 64 ≤ (w 20).val ∧ w 55 = 54 ∧ w 59 = 55)

structure ROMLoadRouting (rom : WordROM) (w : Nat → ZMod mersenne31Modulus) : Prop where
  word : (romAlignedWordTable rom).Contains #[] #v[romWordKey w,w 41,w 42]
  data : SubwordLoad.table.Contains #[] #v[dataKey w (selectedLimb w 41 42),w 44,w 45]

structure RAMLoadRouting (w : Nat → ZMod mersenne31Modulus) : Prop where
  data : SubwordLoad.table.Contains #[] #v[dataKey w (selectedLimb w 32 33),w 41,w 42]
  disabled : #v[w 56,w 57,w 58] = #v[0,0,0]

structure StoreRouting (w : Nat → ZMod mersenne31Modulus) : Prop where
  ram : 64 ≤ (w 20).val
  clear : SubwordStoreClear.table.Contains #[] #v[dataKey w (selectedLimb w 37 38),w 41,w 42]
  place : SubwordStorePlace.table.Contains #[] #v[dataKey w (w 32),w 44,w 45]

end Airbender.SubwordMemory
