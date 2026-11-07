import Human.Helpers.Core.BabyBearPrime
import Human.Trace.UnifiedReduced.RVMixedMemory
import Human.Trace.UnifiedReduced.RVMixedWindowProjection
import Human.Trace.UnifiedReduced.RVPreparedRoundWindows
import Human.Trace.UnifiedReduced.RVCallerCycles

-- The statements proven in slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean (checked by verify.sh). RV
-- siblings of the `Caller.*` claims of `Theorems.lean`. Complete hash-span results (`rvSpanResult`) carry the delegate
-- link: the span's final state IS the spec's run of its `.delegate` calls (`RV.calls`), up to the spec's PC advance.
-- Every caller binding (`RVBinding`) states that the caller's entry decodes to `.delegate k` and that `RV.step` at its
-- PC is `RV.exec` of that call.

namespace Airbender.UnifiedReduced


/-- RV sibling of `Caller.MixedMemorySoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Unified standard/custom instructions, callers and workers share one public
    initialized architecture. Reads, word/address bounds, x0 values and worker
    references are derived through Clean history and actual RV transfers.
    Whole retirement, native ROM shadows and hash spans remain separate. -/
def Caller.RVMixedMemorySoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells),
    Caller.RVMixedMemoryEffects data before cells

/-- RV sibling of `Caller.SharedSpanSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Complete BLAKE G, extended BLAKE and Keccak spans reach their pinned
    references in one actual shared terminal state. The empty ordinary registry
    establishes caller-only rows. Public initialization, mode/span-size ABI,
    modeled tables and logical matching remain visible in `SharedSpanInputs`.
    Worker boundaries, all ranges and intermediate controls are derived.
    This is a memory-effect claim; PC retirement, arbitrary mixed-ISA span
    segmentation and unissued-worker exclusion remain separate. -/
def Caller.RVSharedSpanSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} (accepted : Caller.RVMixedMemoryAccepted data []) (inputs : Caller.RVSharedSpanInputs data before addresses cells span),
    Caller.RVSharedSpanEffects data before cells span

/-- RV sibling of `Caller.RequestWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Unified caller spans match the complete native worker rows between the
    same instruction-boundary cuts. Counts and unique native slots are derived;
    zero-clock surplus effects stay before the cut rather than being excluded. -/
def Caller.RVRequestWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (accepted : Caller.RVRequestChecks data) (inputs : Caller.RVRequestInputs data before addresses) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower),
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper

/-- RV sibling of `Caller.RequestHashWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Unified caller requests and the complete hash reference bind the same native
    window. Public worker initialization, mode/count ABI and worker-only matching
    remain visible; caller control preparation and joint retirement are separate. -/
def Caller.RVRequestHashWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (wordInverse : 64 * (-31457280 : ZMod p) = 1) (byteInverse : 256 * (-7864320 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : Caller.RVRequestChecks data) (workers : Delegation.MemoryAccepted data.workers) (program : Caller.RVRequestInputs data before addresses) (inputs : Caller.rvRequestWindowInputs span data.workers before cells lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned) (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower),
    Caller.RVRequestWindowResult span data.callers data.workers before cells lower upper

/-- RV sibling of `Caller.MixedWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Complete instruction and worker rows between public aligned cuts execute
    in one initialized architectural history. Actual cut states, canonical words,
    retained timestamps and request slots are derived from joint matching.
    This is memory transport; whole caller retirement and hash ABI remain separate. -/
def Caller.RVMixedWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) (ordered : lower ≤ upper),
    Caller.RVMixedWindowExecution data before cells lower upper

/-- RV sibling of `Caller.JointHashWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Caller-only hash windows reach their complete pinned reference at the
    actual joint cut states. Shared matching derives worker boundaries, entry
    controls and round masks. Public mode/count, prefix scope and modeled tables
    remain explicit; ordinary control preparation and ISA retirement are separate. -/
def Caller.RVJointHashWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : Caller.RVMixedMemoryAccepted data []) (inputs : Caller.RVJointHashWindowInputs data before addresses cells span lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper),
    Caller.RVJointHashWindowResult data before cells span lower upper

/-- RV sibling of `Caller.WindowProjectionSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Projected worker memory retains the joint states and native timestamps.
    The empty ordinary registry derives caller-only rows; no independent worker
    matching or boundary values are supplied. -/
def Caller.RVWindowProjectionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.RVMixedMemoryAccepted data []) (inputs : Caller.RVMixedMemoryInputs data [] before ca oa cells) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper),
    Caller.RVProjectedWindowExecution data before cells lower upper

/-- RV sibling of `Caller.WindowScheduleSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Accepted state matching counts every instruction between the public cuts.
    The four-tick duration and request matching derive a caller-only region
    without supplying selectors or an instruction schedule. -/
def Caller.RVWindowScheduleSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)} (accepted : Caller.RVRequestChecks data) (inputs : Caller.RVRequestInputs data before addresses) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.RVCallerWindowSchedule data lower upper

/-- RV sibling of `Caller.MixedWindowProjectionSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Caller regions within mixed history derive worker matching and retained
    boundary images at the actual cut states. Earlier ordinary effects remain
    in the joint prefix; complete hash entry protocols and retirement are separate. -/
def Caller.RVMixedWindowProjectionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.RVMixedProjectedWindowExecution data before cells lower upper

/-- RV sibling of `Caller.ControlPreparationSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Public RV ADDI-from-x0/LUI decoding and accepted native writes prepare
    the actual control at the prepared cut, retaining earlier worker effects.
    Public literal, arithmetic or sequential registries admit successive preparations.
    Native PC/clock matching identifies the literal row; its timestamp survives. Program and final-cycle scope
    remain explicit, with no desired control read or row selector as an input. -/
def Caller.RVControlPreparationSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {register : BitVec 5} {literal : Caller.ControlLiteral} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (scope : Caller.RVControlPreparation data program cut register literal) (nonzero : register ≠ 0) (aligned : cut % 4 = 0),
    Caller.RVPreparedBoundaryExecution data before cells cut register literal

/-- RV sibling of `Caller.ControlPreparationWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Two prepared controls use the same actual states and intervening native
    history. Decoding, matching and public preparation cuts derive both controls. -/
def Caller.RVControlPreparationWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {lower upper : Nat} {firstRegister lastRegister : BitVec 5} {firstLiteral lastLiteral : Caller.ControlLiteral} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (firstScope : Caller.RVControlPreparation data program lower firstRegister firstLiteral) (lastScope : Caller.RVControlPreparation data program upper lastRegister lastLiteral) (firstNonzero : firstRegister ≠ 0) (lastNonzero : lastRegister ≠ 0) (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper),
    Caller.RVPreparedControlWindow data before cells lower upper firstRegister firstLiteral lastRegister lastLiteral

/-- RV sibling of `Caller.MixedWindowChainSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Two native windows and their intervening gap form one actual memory execution
    from public initialization. Every cut state and retained boundary is derived. -/
def Caller.RVMixedWindowChainSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {a b c d : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (positive : 2 ≤ a) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d),
    Caller.RVMixedWindowChainExecution data before cells a b c d

/-- RV sibling of `Caller.MixedWindowSequenceSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). An ordered finite list of native windows and gaps executes continuously
    from public initialization. Matching derives every actual boundary and clock;
    instruction retirement and protocol shape remain separate. -/
def Caller.RVMixedWindowSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {windows : List (Nat × Nat)} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (first : cut % 4 = 0) (positive : 2 ≤ cut) (ordered : Caller.WindowsOrdered cut windows),
    Caller.RVMixedWindowSequenceExecution data before cells cut windows

/-- RV sibling of `Caller.PreparedHashWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Complete G and Keccak references reach the actual mixed-history cut states
    after public RV literal preparation. Shared matching derives controls,
    caller scheduling, worker boundaries and native reads. Other nonround workers
    may precede or follow the homogeneous selected span. Public span ABI,
    program/domain and modeled tables remain explicit; no worker masks are supplied. -/
def Caller.RVPreparedHashWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program span lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0),
    Caller.RVJointHashWindowResult data before cells span lower upper

/-- RV sibling of `Caller.PreparedHashChainSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Two complete prepared G/Keccak references compose through one continuous
    history, including the intervening preparation and other worker effects.
    Public mode/count/duration and nonround worker scope remain explicit. -/
def Caller.RVPreparedHashChainSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {firstSpan secondSpan : Delegation.Caller.HashSpan} {a b c d : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (firstInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program firstSpan a b) (secondInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program secondSpan c d) (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c),
    Caller.RVPreparedHashChainResult data before cells firstSpan secondSpan a b c d

/-- RV sibling of `Caller.PreparedHashSequenceSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). A nonempty ordered list of complete prepared G/Keccak references shares one
    continuous actual memory history. Each span retains its public preparation,
    mode/count/duration and nonround scope; all intermediate states are derived. -/
def Caller.RVPreparedHashSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (accepted : Caller.RVMixedMemoryAccepted data program) (firstInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper) (restInputs : ∀ window ∈ rest, Caller.RVPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper) (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

/-- RV sibling of `Caller.PreparedRoundRegionMasksSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Public LUI preparation and raw joint matching derive exclusive masks within
    one caller region. Its local ten-position bound remains explicit; earlier
    workers, including other families, remain outside the selected region. -/
def Caller.RVPreparedRoundRegionMasksSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {region : Caller.RoundRegion} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (scope : Caller.RVRoundRegionInputs data program region),
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- RV sibling of `Caller.PreparedProtocolSequenceSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Complete prepared G, extended-BLAKE and Keccak lists share one continuous
    actual memory execution. Every extended-round worker must belong to an
    explicit prepared controller region; raw matching derives its mask first.
    Public preparation/protocol shape stays visible, with whole retirement separate. -/
def Caller.RVPreparedProtocolSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (scopes : ∀ window ∈ first :: rest, Caller.RVPreparedProtocolWindowInputs data program window) (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

/-- RV sibling of `Caller.PreparedRoundMasksSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Public LUI preparation and native matching derive all extended-BLAKE masks
    before RV transport. The public suffix duration and ten-position ABI remain explicit. -/
def Caller.RVPreparedRoundMasksSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0),
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- RV sibling of `Caller.PreparedRoundWindowSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Complete extended-BLAKE compression reaches the actual prepared mixed-history
    cut states. Controls, masks, caller selectors and worker boundaries are derived. -/
def Caller.RVPreparedRoundWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower upper : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedRoundWindowInputs data before ca oa cells program flags lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0),
    Caller.RVJointHashWindowResult data before cells (.blakeRound flags) lower upper

/-- RV sibling of `Caller.CallerCyclesSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Actual caller fetch, issued-worker references and RV PC retirement use
    one shared history; each caller's entry decodes to `.delegate k` and `RV.step` at its pre-state is that call. The
    existing worker ABI remains explicit. Sail's code-domain premise (`CodeProfile`) is dropped: the RV ROM image is
    separate from RAM, and the RV table's fetch guard places entries in aligned ROM words. -/
def Caller.RVCallerCyclesSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {initial : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVMixedMemoryInputs data program initial ca oa cells) (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value),
    Caller.RVCallerCycleEffects data program initial cells

/-- RV sibling of `Caller.PreparedRoundCyclesSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). The prepared extended-round scope derives masks before constructing the
    same actual caller cycles; no mask or intermediate state is supplied. No code-domain premise (as above). -/
def Caller.RVPreparedRoundCyclesSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {initial : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {flags : Fin 8} {lower : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedRoundInputs data initial ca oa cells program flags lower) (first : lower % 4 = 0) (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value),
    Caller.RVCallerCycleEffects data program initial cells

/-- RV sibling of `Caller.ProgramWindowScheduleSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Public sequential code identifies a caller region; native matching derives
    its worker family, exact counts and slots without a supplied worker duration. -/
def Caller.RVProgramWindowScheduleSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {family : Delegation.Family} {lower upper : Nat} (accepted : Caller.RVMixedMemoryAccepted data program) (publicProgram : Caller.RVRequestInputs data before ca) (ordinaryProgram : Trace.rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program) (registry : Caller.RVSequentialProgram program) (region : Caller.RVProgramCallerRegion data program family lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value),
    Caller.RVProgramCallerWindow data family lower upper

/-- RV sibling of `Caller.ProgramPreparedProtocolSequenceSoundnessClaim`: states are `RV.State`s, cells are read by `Cell.readRV` and
    executed by `RVHistory`, programs are RV program tables (`RV.decode`), no `Configured`; RAM cells include READ-WRITE
    ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). Public caller regions derive selected worker families and complete call counts
    for all three references in one continuous prepared history. Shared controller
    coverage, public duration/preparation and logical matching remain explicit. -/
def Caller.RVProgramPreparedProtocolSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RVRequestTrace p} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (accepted : Caller.RVMixedMemoryAccepted data program) (inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (registry : Caller.RVSequentialProgram program) (scopes : ∀ window ∈ first :: rest, Caller.RVProgramProtocolWindowInputs data program window) (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

end Airbender.UnifiedReduced
