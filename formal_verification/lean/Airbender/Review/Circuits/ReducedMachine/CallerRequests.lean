import Airbender.Review.Circuits.ReducedMachine.InitializationBatch
import Airbender.Review.Circuits.ReducedMachine.CSR
import Airbender.Review.Helpers.Memory.ReducedMachineCSRCallers

namespace Airbender.NativeCallerRequests
open Airbender.ReducedMachine.Native
abbrev F := ZMod mersenne31Modulus

/-- Actual packed CSR-selector bit, not the physical execute flag. -/
def csrMaskBit (w : Nat → F) : Nat := (w 12).val / 128 % 2

/-- Consequences of the complete native BODY on every ordinary caller row.
    The raw delegation value is not assumed Boolean outside valid decoding.
    Requests from execute0 rows, and all their auxiliary values, remain. -/
structure RowEffects (w : Nat → F) : Prop where
  selector : w 24 = 0 ∨ w 24 = 1
  maskBit : csrMaskBit w = (w 24).val
  multiplicity : (csrRequest w).multiplicity = w 24 * w 65
  kind : (csrRequest w).kind = w 9 * (csrRequest w).multiplicity
  offset : (csrRequest w).offsetHigh = some (w 36 * (csrRequest w).multiplicity)
  clockOffset : (csrRequest w).clockOffset = 3
  zero : (csrRequest w).multiplicity = 0 ↔ w 24 = 0 ∨ w 65 = 0
  requested : (csrRequest w).multiplicity ≠ 0 ↔ w 24 = 1 ∧ w 65 ≠ 0
  disabled : csrMaskBit w = 0 → csrRequest w = ⟨0,0,some 0,3⟩
  present : (csrRequest w).multiplicity ≠ 0 →
    w 24 = 1 ∧ csrMaskBit w = 1 ∧ w 64 = 1 ∧ csrOracleWord w = ⟨0,0⟩

/-- SAME actual full main-list sampling, with no execute/opcode/request filter. -/
def Effects {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) : Prop :=
  ∀ w ∈ Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs proofs), RowEffects w

def terminalClock (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Nat :=
  (Trace.timeOfPair (Airbender.NativeMainStateHistory.state (Airbender.ReducedMachine.NativeMemoryBoundary.finalPCKey inputs)).timestamp).value

/-- Clock consequences on the EXISTING execute1 main-state projection only.
    Every physical request and auxiliary value still remains in Effects; this
    does not assert that every request executes or that a worker was issued. -/
structure ActiveClockEffects {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R))
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  pointwise : ∀ row ∈ Airbender.NativeMainStateHistory.rows (Airbender.NativeInitializationBatch.mainProofs proofs),
    (Trace.timeOfPair (csrCallerObservation row).time).Bounded ∧
      (csrCallerObservation row).clock = row.clock+3 ∧ (csrCallerObservation row).clock % 4 = 3 ∧
      7 ≤ (csrCallerObservation row).clock ∧ (csrCallerObservation row).clock < terminalClock inputs
  unique : ((Airbender.NativeMainStateHistory.rows (Airbender.NativeInitializationBatch.mainProofs proofs)).map
    fun row => (csrCallerObservation row).clock).Nodup
end Airbender.NativeCallerRequests
