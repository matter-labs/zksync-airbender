import Airbender.Review.Circuits.ReducedMachine.LatestReads

namespace Airbender.NativeWorkerWriteSlices
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Two canonical u16 limbs, not a field cast of a whole RV32 word. -/
def WordBound (word : Vector F 2) : Prop := ∀ limb : Fin 2, word[limb].val < 65536

/-- The eight arithmetic state ports9..12 and17..20 remain outside this local
    slice. All43 ports stay in acceptance and the exact memory ledger. -/
def Covered (slot : Fin 43) : Prop := slot.val < 9 ∨ (13 ≤ slot.val ∧ slot.val < 17) ∨ 21 ≤ slot.val

/-- Actual write is bounded or exactly copies BOTH prior value fields. No
    prior word bound or expected worker result is supplied. -/
def PortEffect (w : Nat → F) (slot : Fin 43) : Prop :=
  WordBound (keyValue w slot true) ∨ keyValue w slot true = keyValue w slot false

structure LocalEffects (w : Nat → F) : Prop where
  finalization : w 152 = 0 ∨ w 152 = 1
  ports : ∀ slot, Covered slot → PortEffect w slot

structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  latest : Airbender.NativeLatestReads.Effects proofs batch inputs
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, LocalEffects w
end Airbender.NativeWorkerWriteSlices
