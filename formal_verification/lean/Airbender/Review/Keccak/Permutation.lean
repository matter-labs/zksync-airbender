import Airbender.Review.Keccak.Call
import Airbender.Review.Delegation.Execution
import Clean.Specs.Keccak256

namespace Airbender.Keccak.Permutation
open Trace Reference.RiscV.Sail

/-- Byte offset of one logical Clean lane in Airbender's row-major RAM block.
    Clean numbers lanes column-first; each physical lane occupies eight bytes. -/
def laneOffset (lane : Fin 25) : Nat := 8 * (lane.val / 5 + 5 * (lane.val % 5))

/-- The 25 permutation lanes are successful reads from actual Sail RAM.
    Each lane combines its low and high 32-bit words. These reads and bounds
    are proved from initialized memory matching, not supplied by the caller. -/
def LanesAt (state : State) (pointer : BitVec 32) (lanes : Vector Nat 25) : Prop :=
  ∀ lane : Fin 25, ∃ low high : BitVec 32,
    (Cell.ram (pointer + BitVec.ofNat 32 (laneOffset lane))).read state = .ok low state ∧
    (Cell.ram (pointer + BitVec.ofNat 32 (laneOffset lane) + 4)).read state = .ok high state ∧
    lanes[lane] = low.toNat + 2 ^ 32 * high.toNat ∧ lanes[lane] < 2 ^ 64

/-- Public initial x11 and the initial/final permutation block. This mapping
    is a conclusion of the soundness theorem. Scratch lanes are internal to
    execution and require no assumed initial values. -/
structure WordMapping (initial after : State) (pointer : BitVec 32)
    (input output : Vector Nat 25) : Prop where
  /-- The actual architectural pointer supplied to the request. -/
  pointerRead : (Cell.register 11).read initial = .ok pointer initial
  /-- Initial lanes in the public initialized RAM image. -/
  inputLanes : LanesAt initial pointer input
  /-- Result lanes in actual final RAM. -/
  outputLanes : LanesAt after pointer output


end Airbender.Keccak.Permutation
