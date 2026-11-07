import Airbender.Review.Circuits.Blake2Worker.Capacity

namespace Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native

/-- Source u32 value splitting; timestamps below remain observed base-field
    limbs. Their native raw-u32/M31 representation and ranges are not assumed. -/
def publicWord (word : BitVec 32) : Vector (ZMod mersenne31Modulus) 2 :=
  #v[(word.toNat % 65536 : Nat),(word.toNat / 65536 : Nat)]

structure RegisterObservation where
  value : BitVec 32
  time : Vector (ZMod mersenne31Modulus) 2

/-- All32 returned public register entries, final PC and its timestamp. The x0
    timestamp remains present; the source checks only its returned value zero. -/
structure PublicBoundary where
  registers : Fin 32 → RegisterObservation
  finalPC : BitVec 32
  finalTime : Vector (ZMod mersenne31Modulus) 2

def registerInitialKey (index : Fin 32) : MemoryKey :=
  ⟨⟨1,index.val,0⟩,#v[0,0],#v[0,0]⟩

def registerFinalKey (inputs : PublicBoundary) (index : Fin 32) : MemoryKey :=
  ⟨⟨1,index.val,0⟩,publicWord (inputs.registers index).value,(inputs.registers index).time⟩

def registerProduct {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (key : Fin 32 → MemoryKey) : R :=
  ((List.finRange 32).map fun index => memoryKeyArgument embed memory (key index)).prod

structure PCKey where
  pc : Vector (ZMod mersenne31Modulus) 2
  time : Vector (ZMod mersenne31Modulus) 2
  deriving DecidableEq

structure PCChallenges (R : Type) where
  gamma : R
  high : R
  timeLow : R
  timeHigh : R

/-- Native state-permutation factor uses PC low with literal coefficient1.
    This is separate from the memory factor's register-indicator coefficient1. -/
def pcArgument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : PCChallenges R) (key : PCKey) : R :=
  embed key.pc[0] + ch.high*embed key.pc[1] + ch.timeLow*embed key.time[0] +
    ch.timeHigh*embed key.time[1] + ch.gamma

/-- Exact pinned initial PC0/timestamp4 split at19bits; not a zero-clock PC. -/
def initialPCKey : PCKey := ⟨#v[0,0],#v[4,0]⟩
def finalPCKey (inputs : PublicBoundary) : PCKey := ⟨publicWord inputs.finalPC,inputs.finalTime⟩

/-- Actual successful inverse results returned by the two native boundary
    helpers. Individual worker memory factors are not assumed nonzero. -/
structure BoundaryInverses (R : Type) where
  registers : R
  pc : R

def registerContribution {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (inverse : BoundaryInverses R) : R :=
  registerProduct embed memory registerInitialKey * inverse.registers

def pcContribution {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (pc : PCChallenges R) (inverse : BoundaryInverses R) : R :=
  pcArgument embed pc initialPCKey * inverse.pc

/-- Reviewed source helper contract: successful denominator inverse operations
    and the source public x0-value check. This does not identify these boundary
    tokens with initialized memory history or prove Rust/M31 codec refinement. -/
structure BoundaryAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  x0 : (inputs.registers 0).value = 0
  registers : registerProduct embed memory (registerFinalKey inputs) * inverse.registers = 1
  pc : pcArgument embed pc (finalPCKey inputs) * inverse.pc = 1

/-- Exact native fold: main returned grand claims, worker grand claims, then
    register and PC contributions. Main claims remain full opaque protocol
    outputs, including state/masking/init families, not RAM-only row ratios. -/
def unifiedMemoryAccumulator {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (mains : List R) (batch : WorkerBatch Setup R)
    (inverse : BoundaryInverses R) : R :=
  batch.outputs.foldl (fun accumulator output => accumulator*output.proof.memoryClaim)
    (mains.foldl (·*·) 1) * registerContribution embed memory inverse * pcContribution embed pc inverse

def workerRowProduct {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (proof : DelegationProof R) (write : Bool) : R :=
  ∏ i ∈ Finset.range (constraintsABI.traceLength-1), memoryKeyProduct embed memory (proof.rows i) write

def workerBatchProduct {Setup R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (batch : WorkerBatch Setup R) (write : Bool) : R :=
  (batch.outputs.map fun output => workerRowProduct embed memory output.proof write).prod

/-- Selected source-reference global multiplicative component. All returned
    worker metadata/normalized proofs, full boundary helpers and final native
    accumulator check are retained. No expected token matching, issued stream,
    per-row read/range/clock/result or denominator-nonzero answer is supplied.
    Main auxiliary refinement, other configurations, transcript/physical
    acceptance and cryptographic extraction remain separate. -/
structure UnifiedMemoryAccepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R)
    (config : WorkerConfiguration Setup) (mains : List R) (batch : WorkerBatch Setup R)
    (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  workers : ConfiguredWorkersAccepted embed memory processor config batch
  boundary : BoundaryAccepted embed memory pc inputs inverse
  accumulator : unifiedMemoryAccumulator embed memory pc mains batch inverse = 1

end Airbender.ReducedMachine.NativeMemoryBoundary
