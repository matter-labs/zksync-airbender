module
public import Human.Trace.UnifiedReduced.RVCallerTheorems

/-! The generic-prime forms of the claims of `human/Human/Trace/UnifiedReduced/RVCallerTheorems.lean`, as stated before they were stated at BabyBear
(each premise set forces `p = babyBearModulus`). The slop proofs prove these and instantiate them. -/

@[expose] public section
namespace Airbender.UnifiedReduced
def Caller.RVSharedSpanSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} (_accepted : Caller.RVMixedMemoryAccepted data []) (_inputs : Caller.RVSharedSpanInputs data before addresses cells span),
    Caller.RVSharedSpanEffects data before cells span

def Caller.RVRequestWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : Caller.RVRequestChecks data) (_inputs : Caller.RVRequestInputs data before addresses) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper

def Caller.RVRequestHashWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_wordInverse : 64 * (-31457280 : ZMod p) = 1) (_byteInverse : 256 * (-7864320 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (_accepted : Caller.RVRequestChecks data) (_workers : Delegation.MemoryAccepted data.workers) (_program : Caller.RVRequestInputs data before addresses) (_inputs : Delegation.Caller.HashSpan.RVRequestWindowInputs span data.workers before cells lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    Delegation.Caller.HashSpan.RVRequestWindowResult span data.callers data.workers before cells lower upper

def Caller.RVMixedWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower) (_ordered : lower ≤ upper),
    Caller.RVMixedWindowExecution data before cells lower upper

def Caller.RVJointHashWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data []) (_inputs : Caller.RVJointHashWindowInputs data before addresses cells span lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper),
    Caller.RVJointHashWindowResult data before cells span lower upper

def Caller.RVWindowProjectionSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data []) (_inputs : Caller.RVMixedMemoryInputs data [] before ca oa cells) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper),
    Caller.RVProjectedWindowExecution data before cells lower upper

def Caller.RVWindowScheduleSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : Caller.RVRequestChecks data) (_inputs : Caller.RVRequestInputs data before addresses) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper) (_afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (_beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (_duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.RVCallerWindowSchedule data lower upper

def Caller.RVMixedWindowProjectionSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper) (_afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (_beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (_duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.RVMixedProjectedWindowExecution data before cells lower upper

def Caller.RVControlPreparationSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {register : BitVec 5} {literal : Caller.ControlLiteral} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_scope : Caller.RVControlPreparation data program cut register literal) (_nonzero : register ≠ 0) (_aligned : cut % 4 = 0),
    Caller.RVPreparedBoundaryExecution data before cells cut register literal

def Caller.RVControlPreparationWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {lower upper : Nat} {firstRegister lastRegister : BitVec 5} {firstLiteral lastLiteral : Caller.ControlLiteral} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_firstScope : Caller.RVControlPreparation data program lower firstRegister firstLiteral) (_lastScope : Caller.RVControlPreparation data program upper lastRegister lastLiteral) (_firstNonzero : firstRegister ≠ 0) (_lastNonzero : lastRegister ≠ 0) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_ordered : lower ≤ upper),
    Caller.RVPreparedControlWindow data before cells lower upper firstRegister firstLiteral lastRegister lastLiteral

def Caller.RVMixedWindowSequenceSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) (_rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {windows : List (Nat × Nat)} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_first : cut % 4 = 0) (_positive : 2 ≤ cut) (_ordered : Caller.WindowsOrdered cut windows),
    Caller.RVMixedWindowSequenceExecution data before cells cut windows

def Caller.RVPreparedHashWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program span lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0),
    Caller.RVJointHashWindowResult data before cells span lower upper

def Caller.RVPreparedHashSequenceSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (_accepted : Caller.RVMixedMemoryAccepted data program) (_firstInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper) (_restInputs : ∀ window ∈ rest, Caller.RVPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper) (_ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

def Caller.RVPreparedRoundRegionMasksSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {region : Caller.RoundRegion} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (_scope : Caller.RVRoundRegionInputs data program region),
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round

def Caller.RVPreparedProtocolSequenceSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (_scopes : ∀ window ∈ first :: rest, Caller.RVPreparedProtocolWindowInputs data program window) (_ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

def Caller.RVPreparedRoundMasksSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 8388608 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedRoundInputs data before ca oa cells program flags lower) (_first : lower % 4 = 0),
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round

def Caller.RVPreparedRoundWindowSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedRoundWindowInputs data before ca oa cells program flags lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0),
    Caller.RVJointHashWindowResult data before cells (.blakeRound flags) lower upper

def Caller.RVProgramWindowScheduleSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {family : Delegation.Family} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_publicProgram : Caller.RVRequestInputs data before ca) (_ordinaryProgram : Trace.rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program) (_registry : Caller.RVSequentialProgram program) (_region : Caller.RVProgramCallerRegion data program family lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper) (_afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (_beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value),
    Caller.RVProgramCallerWindow data family lower upper

def Caller.RVProgramPreparedProtocolSequenceSoundnessClaimGeneric : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 16777216 ≤ p) (_clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (_registry : Caller.RVSequentialProgram program) (_scopes : ∀ window ∈ first :: rest, Caller.RVProgramProtocolWindowInputs data program window) (_ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

end Airbender.UnifiedReduced
