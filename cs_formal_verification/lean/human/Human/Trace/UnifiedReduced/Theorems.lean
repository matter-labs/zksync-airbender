import Human.Helpers.Core.BabyBearPrime
import Human.Trace.Delegation.RequestHashWindows
import Human.Trace.UnifiedReduced.CallerCycles
import Human.Trace.UnifiedReduced.Execution
import Human.Trace.UnifiedReduced.MixedMemory
import Human.Trace.UnifiedReduced.MixedWindowProjection
import Human.Trace.UnifiedReduced.PreparedRoundWindows
import Human.Trace.UnifiedReduced.SharedSpans

-- The statements proven in slop/Slop/Final/Trace/UnifiedReduced/Theorems.lean (checked by verify.sh).

namespace Airbender.UnifiedReduced

/-- Standard instructions and project TRIADD/XORROT retire in one trace, with
    their original public Sail decoding and shared initialized history. Final
    PC/cells agree with native terminal tokens; readonly ROM uses actual public
    bytes rather than zero shadow slots. `Mixed.Inputs` contains only the shared
    public boot/configuration/profile conditions. No row reads, bounds, decoded
    results or expected outputs are assumptions. Delegation callers are outside
    this registry. -/
def Mixed.ExecutionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (byteInverse : 256 * (-7864320 : ZMod p) = 1) {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry} (inputs : Mixed.Inputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : Decoded trace program),
    Trace.Realizes (Mixed.Step program) trace initial cells (Trace.ROMView.token initial)

/-- Every admitted native row, in its history-derived order, executes the original
    Sail instruction fetched from public bytes. The final PC and all tracked
    cells match the declared terminal tokens; readonly ROM uses its public bytes.
    `ExecutionInputs` lists public boot/configuration/profile conditions. Reads,
    selectors and word bounds are proved internally from the imported artifact,
    modeled tables and logical matching. No terminal-PC normalization is needed. -/
def ExecutionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (byteInverse : 256 * (-7864320 : ZMod p) = 1) {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry} (inputs : ExecutionInputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : Decoded trace program),
    Trace.Realizes (Step program) trace initial cells (Trace.ROMView.token initial)

open Airbender.Reference.RiscV

/-- Unified standard/custom instructions, callers and workers share one public
    initialized architecture. Reads, word/address bounds, x0 values and worker
    references are derived through Clean history and actual Sail transfers.
    Whole retirement, native ROM shadows and hash spans remain separate. -/
def Caller.MixedMemorySoundnessClaim : Prop :=
  ∀ {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells),
    Caller.MixedMemoryEffects data before cells

/-- Complete BLAKE G, extended BLAKE and Keccak spans reach their pinned
    references in one actual shared terminal state. The empty ordinary registry
    establishes caller-only rows. Public initialization, mode/span-size ABI,
    modeled tables and logical matching remain visible in `SharedSpanInputs`.
    Worker boundaries, all ranges and intermediate controls are derived.
    This is a memory-effect claim; PC retirement, arbitrary mixed-ISA span
    segmentation and unissued-worker exclusion remain separate. -/
def Caller.SharedSpanSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} (accepted : Caller.MixedMemoryAccepted data []) (inputs : Caller.SharedSpanInputs data before addresses cells span),
    Caller.SharedSpanEffects data before cells span

/-- Unified caller spans match the complete native worker rows between the
    same instruction-boundary cuts. Counts and unique native slots are derived;
    zero-clock surplus effects stay before the cut rather than being excluded. -/
def Caller.RequestWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower),
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper

/-- Unified caller requests and the complete hash reference bind the same native
    window. Public worker initialization, mode/count ABI and worker-only matching
    remain visible; caller control preparation and joint retirement are separate. -/
def Caller.RequestHashWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (wordInverse : 64 * (-31457280 : ZMod p) = 1) (byteInverse : 256 * (-7864320 : ZMod p) = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : Caller.RequestChecks data) (workers : Delegation.MemoryAccepted data.workers) (program : Caller.RequestInputs data before addresses) (inputs : span.RequestWindowInputs data.workers before cells lower upper) (aligned : ∀ cell ∈ cells, cell.Aligned) (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower),
    span.RequestWindowResult data.callers data.workers before cells lower upper

/-- Complete instruction and worker rows between public aligned cuts execute
    in one initialized architectural history. Actual cut states, canonical words,
    retained timestamps and request slots are derived from joint matching.
    This is memory transport; whole caller retirement and hash ABI remain separate. -/
def Caller.MixedWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) (ordered : lower ≤ upper),
    Caller.MixedWindowExecution data before cells lower upper

/-- Caller-only hash windows reach their complete pinned reference at the
    actual joint cut states. Shared matching derives worker boundaries, entry
    controls and round masks. Public mode/count, prefix scope and modeled tables
    remain explicit; ordinary control preparation and ISA retirement are separate. -/
def Caller.JointHashWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : Caller.MixedMemoryAccepted data []) (inputs : Caller.JointHashWindowInputs data before addresses cells span lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper),
    Caller.JointHashWindowResult data before cells span lower upper

/-- Projected worker memory retains the joint states and native timestamps.
    The empty ordinary registry derives caller-only rows; no independent worker
    matching or boundary values are supplied. -/
def Caller.WindowProjectionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.MixedMemoryAccepted data []) (inputs : Caller.MixedMemoryInputs data [] before ca oa cells) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper),
    Caller.ProjectedWindowExecution data before cells lower upper

/-- Accepted state matching counts every instruction between the public cuts.
    The four-tick duration and request matching derive a caller-only region
    without supplying selectors or an instruction schedule. -/
def Caller.WindowScheduleSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)} (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.CallerWindowSchedule data lower upper

/-- Caller regions within mixed history derive worker matching and retained
    boundary images at the actual cut states. Earlier ordinary effects remain
    in the joint prefix; complete hash entry protocols and retirement are separate. -/
def Caller.MixedWindowProjectionSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.MixedProjectedWindowExecution data before cells lower upper

/-- Original public ADDI-from-x0/LUI decoding and accepted native writes prepare
    the actual control at the prepared cut, retaining earlier worker effects.
    Public literal, arithmetic or sequential registries admit successive preparations.
    Native PC/clock matching identifies the literal row; its timestamp survives. Program and final-cycle scope
    remain explicit, with no desired control read or row selector as an input. -/
def Caller.ControlPreparationSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {register : BitVec 5} {literal : Caller.ControlLiteral} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells) (scope : Caller.ControlPreparation data program cut register literal) (nonzero : register ≠ 0) (aligned : cut % 4 = 0),
    Caller.PreparedBoundaryExecution data before cells cut register literal

/-- Two prepared controls use the same actual states and intervening native
    history. Decoding, matching and public preparation cuts derive both controls. -/
def Caller.ControlPreparationWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {lower upper : Nat} {firstRegister lastRegister : BitVec 5} {firstLiteral lastLiteral : Caller.ControlLiteral} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells) (firstScope : Caller.ControlPreparation data program lower firstRegister firstLiteral) (lastScope : Caller.ControlPreparation data program upper lastRegister lastLiteral) (firstNonzero : firstRegister ≠ 0) (lastNonzero : lastRegister ≠ 0) (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper),
    Caller.PreparedControlWindow data before cells lower upper firstRegister firstLiteral lastRegister lastLiteral

/-- Two native windows and their intervening gap form one actual memory execution
    from public initialization. Every cut state and retained boundary is derived. -/
def Caller.MixedWindowChainSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {a b c d : Nat} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells) (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (positive : 2 ≤ a) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d),
    Caller.MixedWindowChainExecution data before cells a b c d

/-- An ordered finite list of native windows and gaps executes continuously
    from public initialization. Matching derives every actual boundary and clock;
    instruction retirement and protocol shape remain separate. -/
def Caller.MixedWindowSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {windows : List (Nat × Nat)} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program before ca oa cells) (first : cut % 4 = 0) (positive : 2 ≤ cut) (ordered : Caller.WindowsOrdered cut windows),
    Caller.MixedWindowSequenceExecution data before cells cut windows

/-- Complete G and Keccak references reach the actual mixed-history cut states
    after original public literal preparation. Shared matching derives controls,
    caller scheduling, worker boundaries and native reads. Other nonround workers
    may precede or follow the homogeneous selected span. Public span ABI,
    program/domain and modeled tables remain explicit; no worker masks are supplied. -/
def Caller.PreparedHashWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedHashWindowInputs data before ca oa cells program span lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0),
    Caller.JointHashWindowResult data before cells span lower upper

/-- Two complete prepared G/Keccak references compose through one continuous
    history, including the intervening preparation and other worker effects.
    Public mode/count/duration and nonround worker scope remain explicit. -/
def Caller.PreparedHashChainSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {firstSpan secondSpan : Delegation.Caller.HashSpan} {a b c d : Nat} (accepted : Caller.MixedMemoryAccepted data program) (firstInputs : Caller.PreparedHashWindowInputs data before ca oa cells program firstSpan a b) (secondInputs : Caller.PreparedHashWindowInputs data before ca oa cells program secondSpan c d) (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c),
    Caller.PreparedHashChainResult data before cells firstSpan secondSpan a b c d

/-- A nonempty ordered list of complete prepared G/Keccak references shares one
    continuous actual memory history. Each span retains its public preparation,
    mode/count/duration and nonround scope; all intermediate states are derived. -/
def Caller.PreparedHashSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (accepted : Caller.MixedMemoryAccepted data program) (firstInputs : Caller.PreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper) (restInputs : ∀ window ∈ rest, Caller.PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper) (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.PreparedHashSequenceResult data before cells first rest

/-- Public LUI preparation and raw joint matching derive exclusive masks within
    one caller region. Its local ten-position bound remains explicit; earlier
    workers, including other families, remain outside the selected region. -/
def Caller.PreparedRoundRegionMasksSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion} {region : Caller.RoundRegion} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedProtocolInputs data before ca oa cells program regions) (scope : Caller.RoundRegionInputs data program region),
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- Complete prepared G, extended-BLAKE and Keccak lists share one continuous
    actual memory execution. Every extended-round worker must belong to an
    explicit prepared controller region; raw matching derives its mask first.
    Public preparation/protocol shape stays visible, with whole retirement separate. -/
def Caller.PreparedProtocolSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedProtocolInputs data before ca oa cells program regions) (scopes : ∀ window ∈ first :: rest, Caller.PreparedProtocolWindowInputs data program window) (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.PreparedHashSequenceResult data before cells first rest

/-- Public LUI preparation and native matching derive all extended-BLAKE masks
    before Sail transport. The public suffix duration and ten-position ABI remain explicit. -/
def Caller.PreparedRoundMasksSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0),
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- Complete extended-BLAKE compression reaches the actual prepared mixed-history
    cut states. Controls, masks, caller selectors and worker boundaries are derived. -/
def Caller.PreparedRoundWindowSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower upper : Nat} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedRoundWindowInputs data before ca oa cells program flags lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0),
    Caller.JointHashWindowResult data before cells (.blakeRound flags) lower upper

/-- Actual caller fetch, issued-worker references and Sail PC retirement use
    one shared history. The physical/code domain and existing worker ABI remain explicit. -/
def Caller.CallerCyclesSoundnessClaim : Prop :=
  ∀ {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.MixedMemoryInputs data program initial ca oa cells) (code : Caller.CodeProfile data program cells) (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value),
    Caller.CallerCycleEffects data program initial cells

/-- The prepared extended-round scope derives masks before constructing the
    same actual caller cycles; no mask or intermediate state is supplied. -/
def Caller.PreparedRoundCyclesSoundnessClaim : Prop :=
  ∀ {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {flags : Fin 8} {lower : Nat} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedRoundInputs data initial ca oa cells program flags lower) (first : lower % 4 = 0) (code : Caller.CodeProfile data program cells) (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value),
    Caller.CallerCycleEffects data program initial cells

/-- Public sequential code identifies a caller region; native matching derives
    its worker family, exact counts and slots without a supplied worker duration. -/
def Caller.ProgramWindowScheduleSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {family : Delegation.Family} {lower upper : Nat} (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca) (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.SequentialProgram program) (region : Caller.ProgramCallerRegion data program family lower upper) (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value),
    Caller.ProgramCallerWindow data family lower upper

/-- Public caller regions derive selected worker families and complete call counts
    for all three references in one continuous prepared history. Shared controller
    coverage, public duration/preparation and logical matching remain explicit. -/
def Caller.ProgramPreparedProtocolSequenceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 16777216 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (accepted : Caller.MixedMemoryAccepted data program) (inputs : Caller.PreparedProtocolInputs data before ca oa cells program regions) (registry : Caller.SequentialProgram program) (scopes : ∀ window ∈ first :: rest, Caller.ProgramProtocolWindowInputs data program window) (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.PreparedHashSequenceResult data before cells first rest

end Airbender.UnifiedReduced
