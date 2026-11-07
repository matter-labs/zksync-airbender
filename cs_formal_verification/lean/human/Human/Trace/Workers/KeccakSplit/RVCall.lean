import Human.Circuits.KeccakSplit.Call
import Human.Helpers.Memory.RVAtomicWrites

/-! RV siblings of `Call.ArgumentsAt` and `Call.ExecutesAt` (`Human/Circuits/KeccakSplit/Call.lean`): one documented
    split call on `RV.State`s; the state block is RAM at any address, INCLUDING THE SHADOW RAM BELOW `ROM_END`. -/

namespace Airbender.Keccak.Split.Call
open Trace

/-- RV sibling of `ArgumentsAt`: x10 holds call `index`'s control word, x11 a 256-byte aligned pointer. -/
def RVArgumentsAt (index : Nat) (state : RV.State) : Prop :=
  ∃ control pointer : BitVec 32,
    (Cell.register 10).readRV state = some control ∧
    (Cell.register 11).readRV state = some pointer ∧
    control = BitVec.ofNat 32 (controlAt index) ∧ pointer.toNat % 256 = 0

/-- RV sibling of `ExecutesAt`: from `before` call `index` has its arguments, reads the 64-bit lanes `input` at its
    slots, and `after` is `before` with exactly `writes` applied (`RVAtomicWrites`). -/
def RVExecutesAt (index : Fin 361) (before after : RV.State) : Prop :=
  ∃ (pointer : BitVec 32) (input : Vector Nat 7),
    RVArgumentsAt index.val before ∧
    (Cell.register 11).readRV before = some pointer ∧
    (∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) →
      input[lane] < 2 ^ 64 ∧
      (laneCell pointer (slots index)[lane] false).readRV before = some (half input[lane] false) ∧
      (laneCell pointer (slots index)[lane] true).readRV before = some (half input[lane] true)) ∧
    RVAtomicWrites (writes index pointer (result index input)) before after

end Airbender.Keccak.Split.Call
