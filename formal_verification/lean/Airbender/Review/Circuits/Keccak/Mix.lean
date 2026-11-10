import Airbender.Review.Circuits.Keccak.Theta
import Airbender.Review.Circuits.Keccak.ControlUpdate

namespace Airbender.Keccak

/-- The four actual sixteen-bit fields of one native lane. A lane uses two
    consecutive word ports; field equality binds their memory tokens before
    packing them into a sixty-four-bit value. -/
def readLaneLimbs {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) : Vector (ZMod p) 4 :=
  (#v[15, 16, 19, 20] : Vector Nat 4).map fun start => w (start + 8 * lane.val)

def writeLaneLimbs {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) : Vector (ZMod p) 4 :=
  (#v[17, 18, 21, 22] : Vector Nat 4).map fun start => w (start + 8 * lane.val)

/-- Two native calls form the five Theta D lanes. The first reads the five
    column parities; the second reads the first call's six written lanes,
    including scratch. `transport` binds actual limbs, not expected results.
    The original x10 input fixes the first mode; its actual control write feeds
    the second call and fixes that mode too. Global memory and scheduling remain
    separate; no operand range or D-result assumption is supplied. -/
structure MixMapping {p : Nat} (c : Vector Nat 5) (round : Fin 32)
    (first second : Nat → ZMod p) : Prop where
  firstActive : first Variables.execute = 1
  secondActive : second Variables.execute = 1
  firstControl : (first 3).val = (ControlState.mk 1 0 round).packed
  controlTransport : second 3 = first 5
  parities : ∀ i : Fin 5, readLane first ⟨i.val, by omega⟩ = c[i]
  transport : ∀ i : Fin 6, readLaneLimbs second i = writeLaneLimbs first i

/-- Put the actual five D writes in the column order used by Clean's reference. -/
def dWrites {p : Nat} (first second : Nat → ZMod p) : Vector Nat 5 :=
  #v[writeLane second 4, writeLane first 0, writeLane second 1,
    writeLane first 2, writeLane second 3]

/-- The two calls produce all five lanes of the original `thetaD` reference.
    The first call preserves columns 1/3/4; the second preserves lanes 0/2/5. -/
def MixResult {p : Nat} (c : Vector Nat 5) (first second : Nat → ZMod p) : Prop :=
  dWrites first second = Specs.Keccak256.thetaD c ∧
  (∀ i : Fin 3, writeLaneLimbs first (#v[1, 3, 4] : Vector (Fin 6) 3)[i] =
    readLaneLimbs first (#v[1, 3, 4] : Vector (Fin 6) 3)[i]) ∧
  (∀ i : Fin 3, writeLaneLimbs second (#v[0, 2, 5] : Vector (Fin 6) 3)[i] =
    readLaneLimbs second (#v[0, 2, 5] : Vector (Fin 6) 3)[i])

end Airbender.Keccak
