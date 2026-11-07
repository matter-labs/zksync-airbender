import Airbender.Review.Circuits.Blake2Worker.AuxiliaryArtifact
import Airbender.Review.Circuits.Blake2Worker.MemoryKeys
import Mathlib.Algebra.BigOperators.Fin

namespace Airbender.Blake2Worker.Native
open AuxiliaryArtifact

structure ProcessorChallenges (R : Type) where
  gamma : R
  abiHigh : R
  timeLow : R
  timeHigh : R

/-- Global stage3 worker denominator. Literal type1991 and gamma are outside
    witness scaling; this differs from the dynamic caller-kind expression. -/
def processorArgument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : ProcessorChallenges R) (w : Nat → ZMod mersenne31Modulus) (tau : R) : R :=
  (ch.abiHigh*embed (w constraintsABI.offsetHigh) +
    ch.timeLow*embed (w constraintsABI.writeTime[0]) +
    ch.timeHigh*embed (w constraintsABI.writeTime[1]))*tau + 1991 + ch.gamma

def processorAuxiliaryTerm {R : Type} [CommRing R] (denominator multiplicity tau accumulator : R) : R :=
  tau*(denominator*accumulator-multiplicity)

def memoryAuxiliaryTerm {R : Type} [CommRing R] (tau previous next readFactor writeFactor : R) : R :=
  tau*(next*readFactor-previous*writeFactor)

def grandProductTerm {R : Type} [CommRing R] (tau current next last : R) : R :=
  tau*(next-current*(tau*last))

def grandBoundaryTerm {R : Type} [CommRing R] (tau accumulator claimed : R) : R :=
  tau*accumulator-claimed

def memoryAuxiliaryColumn (slot : Fin 43) : QuarticColumn := auxiliaryLayout.memory[slot.val]!

/-- The selected ordinary-row chain starts from literal1 at unit normalization,
    not a free previous-row accumulator. Source's initial value is tau inverse. -/
def memoryChainValue {R : Type} [CommRing R] (aux : QuarticColumn → R) (index : Nat) : R :=
  if index = 0 then 1 else aux auxiliaryLayout.memory[index-1]!

def memoryFactor {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) (i : Nat) : R :=
  memoryKeyArgument embed ch (quotientMemoryKey w ⟨i%43,Nat.mod_lt _ (by decide)⟩ write)

/-- Individual reviewed native polynomials at unit normalization, separate from
    the body352equations, physical LDE/quotient/challenge separation and last row.
    All43 factors, OLDREADs and readonly refreshes are retained. -/
structure AuxiliaryRowAccepted {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (w : Nat → ZMod mersenne31Modulus) (aux : QuarticColumn → R) (nextGrand : R) : Prop where
  body : LocalProcessingAccepted w
  processing : processorAuxiliaryTerm (processorArgument embed processor w 1)
    (embed (w constraintsABI.multiplicity)) 1 (aux auxiliaryLayout.processing) = 0
  memorySteps : ∀ slot : Fin 43, memoryAuxiliaryTerm 1
    (memoryChainValue aux slot.val) (aux (memoryAuxiliaryColumn slot))
    (memoryFactor embed memory w false slot.val) (memoryFactor embed memory w true slot.val) = 0
  grandStep : grandProductTerm 1 (aux auxiliaryLayout.grandProduct) nextGrand (memoryChainValue aux 43) = 0

/-- Full selected native domain: ordinary rows0..2^20-2 and a last row carrying
    the public grand-product claim. No claimed value1, expected worker stream,
    initialized reads or global caller-worker ledger is supplied. -/
structure AuxiliaryTraceAccepted {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (w : Nat → Nat → ZMod mersenne31Modulus) (aux : Nat → QuarticColumn → R) (claimed : R) : Prop where
  rows : ∀ i < constraintsABI.traceLength-1,
    AuxiliaryRowAccepted embed memory processor (w i) (aux i) (aux (i+1) auxiliaryLayout.grandProduct)
  first : grandBoundaryTerm 1 (aux 0 auxiliaryLayout.grandProduct) 1 = 0
  last : grandBoundaryTerm 1 (aux (constraintsABI.traceLength-1) auxiliaryLayout.grandProduct) claimed = 0

structure AuxiliaryRowEffects {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (w : Nat → ZMod mersenne31Modulus) (aux : QuarticColumn → R) (next : R) : Prop where
  processing : processorArgument embed processor w 1 * aux auxiliaryLayout.processing = embed (w constraintsABI.multiplicity)
  memoryBalance : memoryChainValue aux 43 * memoryKeyProduct embed memory w false = memoryKeyProduct embed memory w true
  grand : next * memoryKeyProduct embed memory w false = aux auxiliaryLayout.grandProduct * memoryKeyProduct embed memory w true

end Airbender.Blake2Worker.Native
