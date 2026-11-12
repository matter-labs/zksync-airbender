module
public import Human.Trace.Delegation.RVCallerTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/Delegation/RVCallerTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The proven proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.Delegation.Caller
def RVRequestsSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_pcInverse : (-30720 : ZMod p) * 65536 = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : RVRequestAccepted data) (_inputs : RVRequestInputs data before addresses),
    RVRequestBinding data before

def RVRequestMemorySoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_pcInverse : (-30720 : ZMod p) * 65536 = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVRequestAccepted data) (_inputs : RVRequestMemoryInputs data before addresses cells),
    RVRequestExecution data before cells

def RVSharedMemorySoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_pcInverse : (-30720 : ZMod p) * 65536 = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : RVSharedMemoryAccepted data) (_inputs : RVSharedMemoryInputs data before addresses cells),
    RVSharedMemoryEffects data before cells

def RVSharedSpanSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_inverse : (-3840 : ZMod p) * 524288 = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan} (_accepted : RVSharedMemoryAccepted data) (_inputs : RVSharedSpanInputs data before addresses cells span),
    RVSharedSpanEffects data before cells span

def RVWorkerScheduleSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_pcInverse : (-30720 : ZMod p) * 65536 = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : RVRequestChecks data) (_inputs : RVRequestInputs data before addresses),
    RVWorkerSchedule data

def RVRequestWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_pcInverse : (-30720 : ZMod p) * 65536 = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : RVRequestChecks data) (_inputs : RVRequestInputs data before addresses) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    RequestWindowBinding data.callers data.workers lower upper

def RVRequestHashWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_pcInverse : (-30720 : ZMod p) * 65536 = 1) (_wordInverse : 64 * (-31457280 : ZMod p) = 1) (_byteInverse : 256 * (-7864320 : ZMod p) = 1) {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : HashSpan} {lower upper : Nat} (_accepted : RVRequestAccepted data) (_program : RVRequestInputs data before addresses) (_inputs : span.RVRequestWindowInputs data.workers before cells lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    span.RVRequestWindowResult data.callers data.workers before cells lower upper

end Airbender.Delegation.Caller
