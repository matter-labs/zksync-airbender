import Airbender.Review.Circuits.ReducedMachine.Delegation
import Airbender.Review.Circuits.ReducedMachine.MemoryBoundary

namespace Airbender.ReducedMachine.NativeMainAuxiliary
open Native NativeMemoryBoundary Airbender.Blake2Worker Airbender.Blake2Worker.Native

/-- Field-key projection of port metadata. Only the three kernel-bound direct
    native ports below participate; this defines no stage2 indirect refinement. -/
def nativeAddress (w : Nat → ZMod mersenne31Modulus) : Trace.MemoryAddress → MemoryKeyAddress
  | .constantRegister index => ⟨1,index,0⟩
  | .register column => ⟨1,w column,0⟩
  | .mixed column registerOnTrue columns =>
    ⟨if registerOnTrue then w column else 1-w column,w columns[0],w columns[1]⟩
  | .indirect port => ⟨0,(port.rawAddress w).1,(port.rawAddress w).2⟩

def mainPort (slot : Fin 3) : Trace.MemoryPort := importedConstraintsMemoryPorts[slot.val]'(by change slot.val < 3; exact slot.isLt)

def mainMemoryKey (w : Nat → ZMod mersenne31Modulus) (slot : Fin 3) (write : Bool) : MemoryKey :=
  let port := mainPort slot
  let value := (if write then port.writeValue.getD port.readValue else port.readValue).evaluate w
  let time := if write then
      #v[w importedConstraintsTraceColumns.initialTime[0]+(port.clock.offset : Nat),
         w importedConstraintsTraceColumns.initialTime[1]]
    else port.clock.previous.map w
  ⟨nativeAddress w port.address,value,time⟩

def mainMemoryProduct {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) : R :=
  ((List.finRange 3).map fun slot => memoryKeyArgument embed memory (mainMemoryKey w slot write)).prod

def mainPCKey (w : Nat → ZMod mersenne31Modulus) (write : Bool) : PCKey :=
  ⟨(if write then importedConstraintsTraceColumns.finalPC else importedConstraintsTraceColumns.initialPC).map w,
    (if write then importedConstraintsTraceColumns.finalTime else importedConstraintsTraceColumns.initialTime).map w⟩

/-- Initialization is unmasked RAM: zero initial value/time, actual teardown
    values/time, and the SAME actual imported address on both sides. -/
def initializationKey (w : Nat → ZMod mersenne31Modulus) (write : Bool) : MemoryKey :=
  ⟨⟨0,w importedConstraintsArgumentColumns.initialAddress[0],w importedConstraintsArgumentColumns.initialAddress[1]⟩,
    if write then #v[0,0] else importedConstraintsArgumentColumns.terminalValue.map w,
    if write then #v[0,0] else importedConstraintsArgumentColumns.terminalTime.map w⟩

def initializationColumns : List Nat :=
  importedConstraintsArgumentColumns.initialAddress.toList ++
    importedConstraintsArgumentColumns.terminalValue.toList ++ importedConstraintsArgumentColumns.terminalTime.toList

/-- Exact source masking term, retaining both occurrences of half-domain scaling. -/
def permutationMaskTerm {R : Type} [CommRing R] (tau execute previous next : R) : R :=
  tau*(next-(tau*execute)*previous+execute)-1

def mainChainValue {R : Type} [Field R] (aux : QuarticColumn → R) (i : Nat) : R :=
  if i = 0 then 1 else aux callerAuxiliaryLayout.memory[i-1]!

def mainRead {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (w : Nat → ZMod mersenne31Modulus) : R :=
  mainMemoryProduct embed memory w false * pcArgument embed pc (mainPCKey w false)

def mainWrite {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (w : Nat → ZMod mersenne31Modulus) : R :=
  mainMemoryProduct embed memory w true * pcArgument embed pc (mainPCKey w true)

/-- Keep the actual execute polynomial. No Boolean execute or execute1 premise
    is inserted for the full physical ordinary domain. -/
def maskedWrite {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (w : Nat → ZMod mersenne31Modulus) : R :=
  embed (w importedConstraintsTraceColumns.execute)*mainWrite embed memory pc w +
    (1-embed (w importedConstraintsTraceColumns.execute))*mainRead embed memory pc w

def rowFactor {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) : R :=
  memoryKeyArgument embed memory (initializationKey w write) *
    (if write then maskedWrite embed memory pc w else mainRead embed memory pc w)

/-- Selected source chain: three memory slots, state, masking, initialization,
    then the adjacent-row grand product. Complete original native body and six
    extra initialization-padding polynomials remain; no history/results supplied.
    Physical quotient/challenge separation and initialization sorting/range
    arguments are separate. No old worker acceptance transfers to this row. -/
structure RowAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R)
    (w : Nat → ZMod mersenne31Modulus) (aux : QuarticColumn → R) (nextGrand : R) : Prop where
  body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table)
  memorySteps : ∀ slot : Fin 3, memoryAuxiliaryTerm 1 (mainChainValue aux slot.val)
    (aux callerAuxiliaryLayout.memory[slot.val]!)
    (memoryKeyArgument embed memory (mainMemoryKey w slot false))
    (memoryKeyArgument embed memory (mainMemoryKey w slot true)) = 0
  state : memoryAuxiliaryTerm 1 (mainChainValue aux 3) (aux callerAuxiliaryLayout.state)
    (pcArgument embed pc (mainPCKey w false)) (pcArgument embed pc (mainPCKey w true)) = 0
  masking : permutationMaskTerm 1 (embed (w importedConstraintsTraceColumns.execute))
    (aux callerAuxiliaryLayout.state) (aux callerAuxiliaryLayout.masking) = 0
  padding : ∀ column ∈ initializationColumns,
    processingMaskTerm 1 (w importedConstraintsArgumentColumns.addressBorrows[1]) (w column) = 0
  initialization : memoryAuxiliaryTerm 1 (aux callerAuxiliaryLayout.masking) (aux callerAuxiliaryLayout.initialization)
    (memoryKeyArgument embed memory (initializationKey w false))
    (memoryKeyArgument embed memory (initializationKey w true)) = 0
  grand : grandProductTerm 1 (aux callerAuxiliaryLayout.grandProduct) nextGrand
    (aux callerAuxiliaryLayout.initialization) = 0

structure MainProof (R : Type) [Field R] where
  rows : Nat → Nat → ZMod mersenne31Modulus
  auxiliary : Nat → QuarticColumn → R
  grandClaim : R

/-- Actual ordinary2^23-1 domain and source first/last grand boundaries. This
    does not turn every physical row into an active logical execution row. -/
structure Accepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (proof : MainProof R) : Prop where
  rows : ∀ i < callerAuxiliaryLayout.traceLength-1,
    RowAccepted embed memory pc (proof.rows i) (proof.auxiliary i)
      (proof.auxiliary (i+1) callerAuxiliaryLayout.grandProduct)
  first : grandBoundaryTerm 1 (proof.auxiliary 0 callerAuxiliaryLayout.grandProduct) 1 = 0
  last : grandBoundaryTerm 1 (proof.auxiliary (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.grandProduct) proof.grandClaim = 0

def mainRowsProduct {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (proof : MainProof R) (write : Bool) : R :=
  ∏ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1), rowFactor embed memory pc (proof.rows i) write

def mainBatchProduct {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (proofs : List (MainProof R)) (write : Bool) : R :=
  (proofs.map fun proof => mainRowsProduct embed memory pc proof write).prod

/-- SAME returned main claims now carry actual full-domain source auxiliary
    proofs, alongside the existing configured worker/public-boundary component. -/
structure MainWorkerAccepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (pc : PCChallenges R) (config : WorkerConfiguration Setup)
    (mains : List (MainProof R)) (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  mainProofs : ∀ proof ∈ mains, Accepted embed memory pc proof
  global : UnifiedMemoryAccepted embed memory processor pc config (mains.map MainProof.grandClaim) batch inputs inverse

end Airbender.ReducedMachine.NativeMainAuxiliary
