import Airbender.Review.Circuits.ReducedMachine.WorkerWriteSlices

namespace Airbender.NativeWorkerWriteWords
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Every actual port writes two bounded limbs or copies both old value fields.
    Refresh timestamps and all43 ports remain unchanged. -/
structure LocalEffects (w : Nat → F) : Prop where
  slices : Airbender.NativeWorkerWriteSlices.LocalEffects w
  ports : ∀ slot, Airbender.NativeWorkerWriteSlices.PortEffect w slot

structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  prior : Airbender.NativeWorkerWriteSlices.Effects proofs batch inputs
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, LocalEffects w
end Airbender.NativeWorkerWriteWords
