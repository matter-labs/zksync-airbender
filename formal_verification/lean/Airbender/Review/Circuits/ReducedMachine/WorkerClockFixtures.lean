import Airbender.Review.Circuits.Blake2Worker.Processing
import Airbender.Review.Circuits.ReducedMachine.WorkerClockProgress

namespace Airbender.NativeWorkerClockFixtures
abbrev F := ZMod mersenne31Modulus

/-- Full LOCAL worker fixtures, not source proofs or initialized histories.
    False: processing(0,524288), all old times(0,0).
    True: processing(0,0), all old times(0,-1) in the native field.
    Both: multiplicity1, all43 borrows0, all other values0. Zero pointers/aliases,
    all13 round flags0 and control values0 remain visible. -/
def assignment (zeroClock : Bool) (column : Nat) : F :=
  if column = 0 then 1 else if column = 741 then (if zeroClock then 0 else 524288) else
  if 744 ≤ column ∧ column < 871 ∧ (column-744)%3 = 0 then (if zeroClock then -1 else 0) else 0

end Airbender.NativeWorkerClockFixtures
