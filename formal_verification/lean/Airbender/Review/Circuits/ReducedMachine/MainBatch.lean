import Airbender.Review.Circuits.ReducedMachine.WorkerClockProgress

namespace Airbender.NativeMainBatch
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
abbrev F := ZMod mersenne31Modulus

/-- Selected capacity scalar only. No generated/body layout equivalence. -/
def capacity : Nat := callerAuxiliaryLayout.traceLength-1

/-- Pinned MAX_CYCLES: two19bit timestamp columns, two empty access bits. -/
def maxCycles : Nat := 2^(19*2) / 2^2

/-- The actual u32 count indexes its observations BY CONSTRUCTION. This
    normalized source reference is not Rust stream/ProofOutput extraction. -/
structure Batch (R : Type) [Field R] where
  countWord : BitVec 32
  outputs : Vector (Proof R) countWord.toNat

def Batch.proofs {R : Type} [Field R] (batch : Batch R) : List (Proof R) := batch.outputs.toList

/-- Duplicate-preserving actual processed processed; no row/proof fallback. -/
def prefixCycles {R : Type} [Field R] (batch : Batch R) (processed : Nat) : Nat :=
  (batch.proofs.take processed).foldl (fun cycles _ => cycles+capacity) 0

/-- Native main-loop checks: positive read count, EACH accumulated processed below
    MAX_CYCLES, and positive final total. This does not count active requests. -/
def CounterAccepted {R : Type} [Field R] (batch : Batch R) : Prop :=
  0 < batch.countWord.toNat ∧
    (∀ i < batch.countWord.toNat, prefixCycles batch (i+1) < maxCycles) ∧
    0 < prefixCycles batch batch.countWord.toNat

/-- Source counter checks PLUS unchanged complete existing components on the
    SAME constructed actual proof list. Old acceptance is not weakened/changed.
    Setup/metadata/transcript/serialization/physical crypto refinement is separate. -/
structure SourceAccepted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    (batch : Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  counter : CounterAccepted batch
  component : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config batch.proofs workers inputs inverse

structure Effects {R : Type} [Field R] (batch : Batch R) : Prop where
  count : batch.proofs.length = batch.countWord.toNat
  positive : 0 < batch.proofs.length
  maximum : batch.proofs.length ≤ 8192
  counter : prefixCycles batch batch.countWord.toNat = batch.proofs.length*capacity
  limit : prefixCycles batch batch.countWord.toNat < maxCycles
  ordinary : (Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs batch.proofs)).length =
    prefixCycles batch batch.countWord.toNat
  ordinaryBound : (Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs batch.proofs)).length ≤ 68719468544
  u64 : ∀ processed ≤ batch.countWord.toNat, prefixCycles batch processed < 2^64
end Airbender.NativeMainBatch
