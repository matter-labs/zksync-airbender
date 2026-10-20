import Airbender.Review.Circuits.SubwordMemory.RoutingModel
import Airbender.Review.Helpers.Tables.SubwordOffset

namespace Airbender.SubwordMemory
open Verification
set_option autoImplicit false

/-- Original fixed offset/trap query, including the native load and x0 fields. -/
def offsetKey (w : Nat → ZMod mersenne31Modulus) : ZMod mersenne31Modulus :=
  w 19 + 65536 * w 11 + 524288 * (1 - w 12) + 1048576 * w 8

/-- Accepted native mask and its derived size/upper-limb controls. -/
structure OffsetValues (w : Nat → ZMod mersenne31Modulus) : Prop where
  keyBound : (offsetKey w).val < 2097152
  offset : (w 22).val = (offsetKey w).val % 4
  mask : (w 23).val = SubwordOffset.mask (offsetKey w).val
  trapAbsent : SubwordOffset.mask (offsetKey w).val < 4
  size : (w 24).val = SubwordOffset.mask (offsetKey w).val % 2
  upper : (w 25).val = (w 22).val / 2

structure ROMWordValues (rom : WordROM) (w : Nat → ZMod mersenne31Modulus) : Prop where
  keyBound : (romWordKey w).val < 1048576
  low : w 41 = ((rom.word (romWordKey w).val).toNat % 65536 : Nat)
  high : w 42 = ((rom.word (romWordKey w).val).toNat / 65536 : Nat)

/-- Certified candidate values and actual native masked writes. Boolean x0
    decoding and initialized execution are separate connections. -/
structure LoadValues (w : Nat → ZMod mersenne31Modulus) (key : ZMod mersenne31Modulus) : Prop where
  keyBound : key.val < 2097152
  low : w 60 = ((SubwordLoad.limbs key.val).1 : Nat)
  high : w 61 = ((SubwordLoad.limbs key.val).2 : Nat)
  bounds : (w 60).val < 65536 ∧ (w 61).val < 65536
  writeLow : w 39 = (1 - w 8) * w 60
  writeHigh : w 40 = (1 - w 8) * w 61

/-- Native full-word/subword mux, retaining the unselected old RAM limb. -/
def storeLow (w : Nat → ZMod mersenne31Modulus) (cleared placed : ZMod mersenne31Modulus) :=
  w 24 * ((1 - w 25) * (cleared + placed) + w 25 * w 37) + (1 - w 24) * w 32

def storeHigh (w : Nat → ZMod mersenne31Modulus) (cleared placed : ZMod mersenne31Modulus) :=
  w 24 * (w 25 * (cleared + placed) + (1 - w 25) * w 38) + (1 - w 24) * w 33

/-- Clearing and placement values, with actual native store-write assembly.
    Bounds on old/source reads and whole written words come from history later. -/
structure StoreValues (w : Nat → ZMod mersenne31Modulus) : Prop where
  clearKeyBound : (dataKey w (selectedLimb w 37 38)).val < 2097152
  placeKeyBound : (dataKey w (w 32)).val < 2097152
  cleared : w 41 = (SubwordStoreClear.cleared (dataKey w (selectedLimb w 37 38)).val : Nat)
  placed : w 44 = (SubwordStorePlace.placed (dataKey w (w 32)).val : Nat)
  unused : w 42 = 0 ∧ w 45 = 0
  bounds : (w 41).val < 65536 ∧ (w 44).val < 65536
  writeLow : w 39 = storeLow w (w 41) (w 44)
  writeHigh : w 40 = storeHigh w (w 41) (w 44)

end Airbender.SubwordMemory
