module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Delegation.RVSchedule
public import Human.Trace.Delegation.RVRequestEffects
public import Human.Trace.Delegation.RVSharedMemory
public import Human.Trace.Delegation.RVSharedSpans
public import Human.Trace.Delegation.RVMixedMemory
public import Human.Trace.Delegation.RVRequestHashWindows

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Delegation/RVCallerTheorems.lean (checked by verify.sh). The public starting point is an `RV.State`, the caller table is built by `RV.decode` of
-- its ROM image (`rvProgramImage`; a caller row decodes to `.delegate k`, and `RV.step` at its PC is that call), cells
-- are read/written by `Cell.readRV`/`Cell.applyRV` (`RVHistory`), seeds are `initialImageRV`. RAM
-- cells are RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`
-- (`RV.State.delegationRAM`): no pointer is required to be at or above `ROM_END`.

namespace Airbender.Delegation.Caller

/-- Public RV caller instructions (each a `.delegate k` call) are bound to actual
    worker rows of the decoded family through the native request permutation; initialized machine clocks prove
    invocation bounds and write-offset room for the whole worker pool. Zero-clock workers remain an explicit gap. -/
def RVRequestsSoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : RVRequestAccepted data) (_inputs : RVRequestInputs data before addresses),
    RVRequestBinding data before

/-- Caller requests and the worker pool's actual RV memory effects
    (`RVMemoryExecution` from the `initialImageRV` seeds; RAM cells include read-write access to the shadow RAM below
    `ROM_END`). No whole-machine execution or zero-clock fulfillment claim. -/
def RVRequestMemorySoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVRequestAccepted data) (_inputs : RVRequestMemoryInputs data before addresses cells),
    RVRequestExecution data before cells

/-- Decoded RV callers are linked to actual initialized workers whose native
    port effects match the bigint/Clean hash references, inside RV memory execution. BabyBear is explicit. -/
def RVOperationSoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVRequestAccepted data) (_inputs : RVRequestOperationInputs data before addresses cells),
    RVRequestOperationEffects data before cells

/-- Caller and worker GPR/RAM transfers execute in one initialized RV
    history (`RVHistory` from `initialImageRV`; RAM cells include read-write access to the shadow RAM below
    `ROM_END`). Shared matching proves the caller's x0 source and every worker address bound. -/
def RVSharedMemorySoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVSharedMemoryAccepted data) (_inputs : RVSharedMemoryInputs data before addresses cells),
    RVSharedMemoryEffects data before cells

/-- Shared RV initialization, memory matching and RV transfers derive
    every word bound and connect native port values to the four operation references. -/
def RVSharedOperationSoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVSharedMemoryAccepted data) (_inputs : RVSharedOperationInputs data before addresses cells),
    RVSharedOperationEffects data before cells

/-- A complete hash span reaches its reference result in the same final
    `RV.State` that realizes every shared terminal token, and that state IS the spec's run of the span's delegation
    calls from `before` (`HashSpan.RVResult`, up to the spec's PC advance). Only public mode/control and the span-size
    ABI remain. -/
def RVSharedSpanSoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan} (_accepted : RVSharedMemoryAccepted data) (_inputs : RVSharedSpanInputs data before addresses cells span),
    RVSharedSpanEffects data before cells span

/-- Ordinary six-family instructions (RV table) and delegation workers share
    initialized RV architectural memory; shared history supplies every word/address bound, x0 read and RV transfer.
    The word-ROM/subword tables hold the ROM image's words (`romImageRV`, `ROM.wordsRV`). -/
def RVMixedMemorySoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {program : List Trace.RVPooledProgramEntry} {before : RV.State} {callerAddresses ordinaryAddresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVMixedMemoryAccepted data program) (_inputs : RVMixedMemoryInputs data program before callerAddresses ordinaryAddresses cells),
    RVMixedMemoryEffects data before cells

/-- State-free conclusion over RV public inputs: request matching places
    exactly one worker inside each caller's native four-tick cycle; zero-clock workers are classified as unissued. -/
def RVWorkerScheduleSoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : RVRequestChecks data) (_inputs : RVRequestInputs data before addresses),
    RVWorkerSchedule data

/-- State-free conclusion over RV public inputs: instruction-boundary cuts
    select exactly the callers issuing the native worker window. -/
def RVRequestWindowSoundnessClaim : Prop :=
  ∀ {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : RVRequestChecks data) (_inputs : RVRequestInputs data before addresses) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    RequestWindowBinding data.callers data.workers lower upper

/-- The same selected workers bind actual RV caller requests and a
    complete pinned hash reference at derived RV cut states, whose final state IS the spec's run of the span's
    delegation calls (`HashSpan.RVResult`). The public worker-window ABI and worker-only matching remain explicit. -/
def RVRequestHashWindowSoundnessClaim : Prop :=
  ∀    {data : RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan} {lower upper : Nat} (_accepted : RVRequestAccepted data) (_program : RVRequestInputs data before addresses) (_inputs : span.RVRequestWindowInputs data.workers before cells lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    span.RVRequestWindowResult data.callers data.workers before cells lower upper

end Airbender.Delegation.Caller
