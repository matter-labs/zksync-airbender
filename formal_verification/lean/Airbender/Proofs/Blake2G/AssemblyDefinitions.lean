import Mathlib.Data.ZMod.Basic

namespace Airbender.Blake2G.Proofs

def firstAlo {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  w 15 + w 19 + w 33 - 65536 * w 37 - 131072 * w 38

def firstAhi {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  w 16 + w 20 + w 34 + w 37 + 2 * w 38 - 65536 * w 39 - 131072 * w 40

def firstClo {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  w 23 + w 47 + 256 * w 48 - 65536 * w 49

def firstChi {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  w 24 + w 44 + 256 * w 45 + w 49 - 65536 * w 50

def secondAlo {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  firstAlo w + w 59 + 16 * w 62 + 128 * w 63 + w 35 - 65536 * w 65 - 131072 * w 66

def secondAhi {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  firstAhi w + w 64 + 16 * w 57 + 128 * w 58 + w 36 + w 65 + 2 * w 66 -
    65536 * w 67 - 131072 * w 68

def secondClo {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  firstClo w + w 72 + 256 * w 73 - 65536 * w 75

def secondChi {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  firstChi w + w 74 + 256 * w 71 + w 75 - 65536 * w 76

/-- Supply the eight output limbs from the G fragment's existing intermediates.
    This is witness wiring, not another constraint or reference semantics. -/
def assemble {p : Nat} (base : Nat → ZMod p) (column : Nat) : ZMod p :=
  match column with
  | 17 => secondAlo base | 18 => secondAhi base
  | 21 => base 80 + 512 * base 81 | 22 => base 82 + 512 * base 79
  | 25 => secondClo base | 26 => secondChi base
  | 29 => base 72 + 256 * base 73 | 30 => base 74 + 256 * base 71
  | n => base n

end Airbender.Blake2G.Proofs
