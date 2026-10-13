import Airbender.Review.Circuits.Keccak.Controls

namespace Airbender.Keccak

/-- Modes: 0 Iota, 1/2 column mixes, 3 Theta, 4 Rho, 5/6 Chi.
    Five round bits permit 0..31; establishing the
    protocol's 24-round schedule is a separate obligation. -/
structure ControlState where
  mode : Fin 7
  iteration : Fin 5
  round : Fin 32

def ControlState.packed (s : ControlState) : Nat :=
  s.mode.val + 8 * s.iteration.val + 64 * s.round.val

/-- Local progression from keccak_special5/mod.rs's control_next equation.
    Iota/Theta/Rho advance after five iterations; the two Chi modes alternate,
    with the last Chi2 iteration returning to Iota and incrementing the round. -/
def ControlState.nextPacked (s : ControlState) : Nat :=
  let last := s.iteration.val = 4
  let mode := if s.mode.val = 6 then (if last then 0 else 5)
    else if s.mode.val = 1 ∨ s.mode.val = 2 ∨ s.mode.val = 5 then s.mode.val + 1
    else s.mode.val + if last then 1 else 0
  let iteration := if s.mode.val = 0 ∨ s.mode.val = 3 ∨ s.mode.val = 4 ∨ s.mode.val = 6
    then (if last then 0 else s.iteration.val + 1) else s.iteration.val
  let round := s.round.val + if s.mode.val = 6 ∧ last then 1 else 0
  mode + 8 * iteration + 64 * round

/-- Consequences for the actual x10 low-limb read and write. No decoded input,
    output, or control-register range is an assumption. -/
structure ControlUpdateChecks {p : Nat} (w : Nat → ZMod p) : Prop where
  inactive : w 0 = 0 → w 5 = w 3
  active : w 0 = 1 → ∃ s : ControlState,
    (w 3).val = s.packed ∧ (w 5).val = s.nextPacked

end Airbender.Keccak
