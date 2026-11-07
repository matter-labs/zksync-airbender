import Mathlib.Data.ZMod.Basic

namespace Airbender.Arithmetic

def carryLow {p : Nat} (value : ZMod p) : ZMod p := ((value.val % 2 : Nat) : ZMod p)
def carryHigh {p : Nat} (value : ZMod p) : ZMod p := ((value.val / 2 : Nat) : ZMod p)
def combinedLow {p : Nat} (value : ZMod p) : ZMod p := ((value.val % 16 : Nat) : ZMod p)
def combinedHigh {p : Nat} (value : ZMod p) : ZMod p := ((value.val / 16 : Nat) : ZMod p)

end Airbender.Arithmetic
