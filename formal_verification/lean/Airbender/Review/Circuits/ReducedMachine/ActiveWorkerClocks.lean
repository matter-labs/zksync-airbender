import Airbender.Review.Circuits.ReducedMachine.NativeMemoryHistory

namespace Airbender.NativeActiveWorkerClocks
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- BOTH actual raw processing-clock field limbs, with no range interpretation. -/
def workerClock (w : Nat → F) : F × F :=
  (w constraintsABI.writeTime[0],w constraintsABI.writeTime[1])

/-- Actual source of a read clock: an ordinary worker observation and one of its
    ALL43 raw quotient writes. Activity and exact token/clock binding are derived;
    no expected fulfilled-worker stream or initialized read value is supplied. -/
def ActiveWriter {Setup R : Type} [Field R] (batch : WorkerBatch Setup R)
    (token : Trace.MemoryToken mersenne31Modulus) : Prop :=
  ∃ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∃ slot : Fin 43,
    w constraintsABI.multiplicity = 1 ∧
      token = Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true) ∧
      token.time = workerClock w

/-- A sharper consequence on the SAME complete ledger. This isolates active
    raw-worker clocks as the remaining source of unbounded read clocks, rather
    than assuming those clocks bounded or silently dropping inactive workers. -/
structure Effects {Setup R : Type} [Field R] (proofs : List (Proof R)) (batch : WorkerBatch Setup R) : Prop where
  processing : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, LocalProcessingAccepted w
  clocks : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false,
    (Trace.timeOfPair token.time).Bounded ∨ ActiveWriter batch token
  unbounded : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false,
    ¬ (Trace.timeOfPair token.time).Bounded →
      ∃ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∃ slot : Fin 43,
        w constraintsABI.multiplicity = 1 ∧
          token = Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true) ∧
          token.time = workerClock w ∧ ¬ (Trace.timeOfPair (workerClock w)).Bounded

end Airbender.NativeActiveWorkerClocks
