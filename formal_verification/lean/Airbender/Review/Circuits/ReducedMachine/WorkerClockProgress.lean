import Airbender.Review.Circuits.ReducedMachine.ActiveWorkerClocks

namespace Airbender.NativeWorkerClockProgress
open Airbender.Blake2Worker.Native
abbrev F := Airbender.NativeActiveWorkerClocks.F

def clock (w : Nat → F) : Trace.Timestamp :=
  Trace.timeOfPair (Airbender.NativeActiveWorkerClocks.workerClock w)

def readToken (w : Nat → F) (slot : Fin 43) : Trace.MemoryToken mersenne31Modulus :=
  Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot false)

def readClock (w : Nat → F) (slot : Fin 43) : Trace.Timestamp :=
  Trace.timeOfPair (readToken w slot).time

/-- A local progress alternative, NOT supplied old-read or processor bounds. -/
def LocalProgress (w : Nat → F) : Prop :=
  ∀ slot : Fin 43, w constraintsABI.multiplicity = 1 →
    ¬ (clock w).Bounded ∨ ¬ (readClock w slot).Bounded ∨ (readClock w slot).value < (clock w).value

/-- EXACT actual active writer and full token, retaining address/value/BOTH times.
    Unboundedness is derived on the same raw processing clock, not a new bound. -/
def UnboundedWriter {Setup R : Type} [Field R] (batch : WorkerBatch Setup R)
    (token : Trace.MemoryToken mersenne31Modulus) : Prop :=
  ∃ source ∈ Airbender.NativeTokenLedger.workerRows batch, ∃ slot : Fin 43,
    source constraintsABI.multiplicity = 1 ∧
      token = Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey source slot true) ∧
      token.time = Airbender.NativeActiveWorkerClocks.workerClock source ∧ ¬ (clock source).Bounded

/-- Derived alternatives on the SAME complete native batch. No initialized
    history, expected read/fulfilled ledger or worker-clock bound is assumed. -/
structure Effects {Setup R : Type} [Field R]
    (batch : WorkerBatch Setup R) : Prop where
  progress : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
    w constraintsABI.multiplicity = 1 → ∀ slot : Fin 43,
      ¬ (clock w).Bounded ∨ (readClock w slot).value < (clock w).value ∨ UnboundedWriter batch (readToken w slot)
  zero : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
    w constraintsABI.multiplicity = 1 → Airbender.NativeActiveWorkerClocks.workerClock w = (0,0) →
      ∀ slot : Fin 43, UnboundedWriter batch (readToken w slot)
end Airbender.NativeWorkerClockProgress
