module
public import Slop.WordMemory
public import Slop.Trace.Addresses
public import Human.Helpers.Memory.Native
public import Slop.Trace.Family.History

@[expose] public section

namespace Airbender.Trace.ROMView
open Arithmetic

theorem native_clocks {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (hp : 4 < p)
    {trace : Data p Kind} {cells : List Cell}
    (seed : trace.initialMemory = nativeBootImage cells)
    (initial : trace.initial = PCState.boundary 0 (4, 0)) : ClockBoundary trace := by
  constructor
  · rw [initial]
    change (4 : ZMod p).val < timestampBase ∧ (0 : ZMod p).val < timestampBase
    rw [ZMod.val_ofNat_of_lt hp]
    norm_num [timestampBase]
  · rw [initial]
    change ((4 : ZMod p).val + timestampBase * (0 : ZMod p).val) % 4 = 0
    rw [ZMod.val_ofNat_of_lt hp]
    norm_num
  · intro native member
    rw [seed] at member
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
    simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

end Airbender.Trace.ROMView
