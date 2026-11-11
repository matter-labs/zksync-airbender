module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Trace.UnifiedReduced.RVMixedMemory
public import Human.Trace.UnifiedReduced.RVMixedWindowProjection
public import Human.Trace.UnifiedReduced.RVPreparedRoundWindows
public import Human.Trace.UnifiedReduced.RVCallerCycles

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/UnifiedReduced/RVCallerTheorems.lean (checked by verify.sh). Complete hash-span results (`Delegation.Caller.HashSpan.RVResult`) carry the delegate
-- link: the span's final state IS the spec's run of its `.delegate` calls (`RV.calls`), up to the spec's PC advance.
-- Every caller binding (`RVBinding`) states that the caller's entry decodes to `.delegate k` and that `RV.step` at its
-- PC is `RV.exec` of that call.
-- In every claim below, states are `RV.State`s, cells are read by `Cell.readRV` and executed by `RVHistory`, programs
-- are RV program tables (`RV.decode`), and RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`
-- (`RV.State.delegationRAM`).

namespace Airbender.UnifiedReduced


/-- Unified standard/custom instructions, callers and workers share one public
    initialized architecture. Reads, word/address bounds, x0 values and worker
    references are derived through Clean history and actual RV transfers.
    Whole retirement, native ROM shadows and hash spans remain separate. -/
def Caller.RVMixedMemorySoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells),
    Caller.RVMixedMemoryEffects data before cells

/-- Complete BLAKE G, extended BLAKE and Keccak spans reach their pinned
    references in one actual shared terminal state. The empty ordinary registry
    establishes caller-only rows. Public initialization, mode/span-size ABI,
    modeled tables and logical matching remain visible in `RVSharedSpanInputs`.
    Worker boundaries, all ranges and intermediate controls are derived.
    This is a memory-effect claim; PC retirement, arbitrary mixed-ISA span
    segmentation and unissued-worker exclusion remain separate. -/
def Caller.RVSharedSpanSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} (_accepted : Caller.RVMixedMemoryAccepted data []) (_inputs : Caller.RVSharedSpanInputs data before addresses cells span),
    Caller.RVSharedSpanEffects data before cells span

/-- Unified caller spans match the complete native worker rows between the
    same instruction-boundary cuts. Counts and unique native slots are derived;
    zero-clock surplus effects stay before the cut rather than being excluded. -/
def Caller.RVRequestWindowSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : Caller.RVRequestChecks data) (_inputs : Caller.RVRequestInputs data before addresses) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper

/-- Unified caller requests and the complete hash reference bind the same native
    window. Public worker initialization, mode/count ABI and worker-only matching
    remain visible; caller control preparation and joint retirement are separate. -/
def Caller.RVRequestHashWindowSoundnessClaim : Prop :=
  ∀   {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (_accepted : Caller.RVRequestChecks data) (_workers : Delegation.MemoryAccepted data.workers) (_program : Caller.RVRequestInputs data before addresses) (_inputs : Delegation.Caller.HashSpan.RVRequestWindowInputs span data.workers before cells lower upper) (_aligned : ∀ cell ∈ cells, cell.Aligned) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower),
    Delegation.Caller.HashSpan.RVRequestWindowResult span data.callers data.workers before cells lower upper

/-- Complete instruction and worker rows between public aligned cuts execute
    in one initialized architectural history. Actual cut states, canonical words,
    retained timestamps and request slots are derived from joint matching.
    This is memory transport; whole caller retirement and hash ABI remain separate. -/
def Caller.RVMixedWindowSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_pastZero : 2 ≤ lower) (_ordered : lower ≤ upper),
    Caller.RVMixedWindowExecution data before cells lower upper

/-- Caller-only hash windows reach their complete pinned reference at the
    actual joint cut states. Shared matching derives worker boundaries, entry
    controls and round masks. Public mode/count, prefix scope and modeled tables
    remain explicit; ordinary control preparation and ISA retirement are separate. -/
def Caller.RVJointHashWindowSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data []) (_inputs : Caller.RVJointHashWindowInputs data before addresses cells span lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper),
    Caller.RVJointHashWindowResult data before cells span lower upper

/-- Projected worker memory retains the joint states and native timestamps.
    The empty ordinary registry derives caller-only rows; no independent worker
    matching or boundary values are supplied. -/
def Caller.RVWindowProjectionSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data []) (_inputs : Caller.RVMixedMemoryInputs data [] before ca oa cells) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper),
    Caller.RVProjectedWindowExecution data before cells lower upper

/-- Accepted state matching counts every instruction between the public cuts.
    The four-tick duration and request matching derive a caller-only region
    without supplying selectors or an instruction schedule. -/
def Caller.RVWindowScheduleSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {addresses : List (BitVec 32)} (_accepted : Caller.RVRequestChecks data) (_inputs : Caller.RVRequestInputs data before addresses) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper) (_afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (_beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (_duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.RVCallerWindowSchedule data lower upper

/-- Caller regions within mixed history derive worker matching and retained
    boundary images at the actual cut states. Earlier ordinary effects remain
    in the joint prefix; complete hash entry protocols and retirement are separate. -/
def Caller.RVMixedWindowProjectionSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) {lower upper : Nat} (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper) (_afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (_beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) (_duration : upper = lower + 4 * (data.workers.windowRows lower upper).length),
    Caller.RVMixedProjectedWindowExecution data before cells lower upper

/-- Public RV ADDI-from-x0/LUI decoding and accepted native writes prepare
    the actual control at the prepared cut, retaining earlier worker effects.
    Public literal, arithmetic or sequential registries admit successive preparations.
    Native PC/clock matching identifies the literal row; its timestamp survives. Program and final-cycle scope
    remain explicit, with no desired control read or row selector as an input. -/
def Caller.RVControlPreparationSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {register : BitVec 5} {literal : Caller.ControlLiteral} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_scope : Caller.RVControlPreparation data program cut register literal) (_nonzero : register ≠ 0) (_aligned : cut % 4 = 0),
    Caller.RVPreparedBoundaryExecution data before cells cut register literal

/-- Two prepared controls use the same actual states and intervening native
    history. Decoding, matching and public preparation cuts derive both controls. -/
def Caller.RVControlPreparationWindowSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {lower upper : Nat} {firstRegister lastRegister : BitVec 5} {firstLiteral lastLiteral : Caller.ControlLiteral} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_firstScope : Caller.RVControlPreparation data program lower firstRegister firstLiteral) (_lastScope : Caller.RVControlPreparation data program upper lastRegister lastLiteral) (_firstNonzero : firstRegister ≠ 0) (_lastNonzero : lastRegister ≠ 0) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_ordered : lower ≤ upper),
    Caller.RVPreparedControlWindow data before cells lower upper firstRegister firstLiteral lastRegister lastLiteral

/-- An ordered finite list of native windows and gaps executes continuously
    from public initialization. Matching derives every actual boundary and clock;
    instruction retirement and protocol shape remain separate. -/
def Caller.RVMixedWindowSequenceSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat} {windows : List (Nat × Nat)} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_first : cut % 4 = 0) (_positive : 2 ≤ cut) (_ordered : Caller.WindowsOrdered cut windows),
    Caller.RVMixedWindowSequenceExecution data before cells cut windows

/-- Complete G and Keccak references reach the actual mixed-history cut states
    after public RV literal preparation. Shared matching derives controls,
    caller scheduling, worker boundaries and native reads. Other nonround workers
    may precede or follow the homogeneous selected span. Public span ABI,
    program/domain and modeled tables remain explicit; no worker masks are supplied. -/
def Caller.RVPreparedHashWindowSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program span lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0),
    Caller.RVJointHashWindowResult data before cells span lower upper

/-- A nonempty ordered list of complete prepared G/Keccak references shares one
    continuous actual memory history. Each span retains its public preparation,
    mode/count/duration and nonround scope; all intermediate states are derived. -/
def Caller.RVPreparedHashSequenceSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (_accepted : Caller.RVMixedMemoryAccepted data program) (_firstInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper) (_restInputs : ∀ window ∈ rest, Caller.RVPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper) (_ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

/-- Public LUI preparation and raw joint matching derive exclusive masks within
    one caller region. Its local ten-position bound remains explicit; earlier
    workers, including other families, remain outside the selected region. -/
def Caller.RVPreparedRoundRegionMasksSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {region : Caller.RoundRegion} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (_scope : Caller.RVRoundRegionInputs data program region),
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- Complete prepared G, extended-BLAKE and Keccak lists share one continuous
    actual memory execution. Every extended-round worker must belong to an
    explicit prepared controller region; raw matching derives its mask first.
    Public preparation/protocol shape stays visible, with whole retirement separate. -/
def Caller.RVPreparedProtocolSequenceSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (_scopes : ∀ window ∈ first :: rest, Caller.RVPreparedProtocolWindowInputs data program window) (_ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

/-- Public LUI preparation and native matching derive all extended-BLAKE masks
    before RV transport. The public suffix duration and ten-position ABI remain explicit. -/
def Caller.RVPreparedRoundMasksSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedRoundInputs data before ca oa cells program flags lower) (_first : lower % 4 = 0),
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- Complete extended-BLAKE compression reaches the actual prepared mixed-history
    cut states. Controls, masks, caller selectors and worker boundaries are derived. -/
def Caller.RVPreparedRoundWindowSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {flags : Fin 8} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedRoundWindowInputs data before ca oa cells program flags lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0),
    Caller.RVJointHashWindowResult data before cells (.blakeRound flags) lower upper

/-- Actual caller fetch, issued-worker references and RV PC retirement use
    one shared history; each caller's entry decodes to `.delegate k` and `RV.step` at its pre-state is that call. The
    existing worker ABI remains explicit. No code-domain premise is needed: the RV ROM image is
    separate from RAM, and the RV table's fetch guard places entries in aligned ROM words. -/
def Caller.RVCallerCyclesSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {initial : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program initial ca oa cells) (_started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value),
    Caller.RVCallerCycleEffects data program initial cells

/-- The prepared extended-round scope derives masks before constructing the
    same actual caller cycles; no mask or intermediate state is supplied. No code-domain premise (as above). -/
def Caller.RVPreparedRoundCyclesSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {initial : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {flags : Fin 8} {lower : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedRoundInputs data initial ca oa cells program flags lower) (_first : lower % 4 = 0) (_started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value),
    Caller.RVCallerCycleEffects data program initial cells

/-- Public sequential code identifies a caller region; native matching derives
    its worker family, exact counts and slots without a supplied worker duration. -/
def Caller.RVProgramWindowScheduleSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {family : Delegation.Family} {lower upper : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_publicProgram : Caller.RVRequestInputs data before ca) (_ordinaryProgram : Trace.rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program) (_registry : Caller.RVSequentialProgram program) (_region : Caller.RVProgramCallerRegion data program family lower upper) (_first : lower % 4 = 0) (_last : upper % 4 = 0) (_positive : 2 ≤ lower) (_ordered : lower ≤ upper) (_afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower) (_beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value),
    Caller.RVProgramCallerWindow data family lower upper

/-- Public caller regions derive selected worker families and complete call counts
    for all three references in one continuous prepared history. Shared controller
    coverage, public duration/preparation and logical matching remain explicit. -/
def Caller.RVProgramPreparedProtocolSequenceSoundnessClaim : Prop :=
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVPreparedProtocolInputs data before ca oa cells program regions) (_registry : Caller.RVSequentialProgram program) (_scopes : ∀ window ∈ first :: rest, Caller.RVProgramProtocolWindowInputs data program window) (_ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)),
    Caller.RVPreparedHashSequenceResult data before cells first rest

/-! Non-vacuity: the assumptions of the caller claims that need no complete hash span can be met, with a selected
    caller and, for the window claims, a worker row in the window. -/

/-- The assumptions of `Caller.RVMixedMemorySoundnessClaim` can be met, with a caller. -/
def Caller.RVMixedMemorySoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program before ca oa cells ∧
      data.callers ≠ []

/-- The assumptions of `Caller.RVRequestWindowSoundnessClaim` can be met, with a caller and a worker row in the
    window. -/
def Caller.RVRequestWindowSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (addresses : List (BitVec 32)) (lower upper : Nat),
    Caller.RVRequestChecks data ∧ Caller.RVRequestInputs data before addresses ∧ lower % 4 = 0 ∧ upper % 4 = 0 ∧
      2 ≤ lower ∧ data.callers ≠ [] ∧ data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVMixedWindowSoundnessClaim` can be met, with a caller and a worker row in the
    window. -/
def Caller.RVMixedWindowSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell) (lower upper : Nat),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program before ca oa cells ∧
      lower % 4 = 0 ∧ upper % 4 = 0 ∧ 2 ≤ lower ∧ lower ≤ upper ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVWindowProjectionSoundnessClaim` can be met, with a caller and a worker row in the
    window. -/
def Caller.RVWindowProjectionSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell) (lower upper : Nat),
    Caller.RVMixedMemoryAccepted data [] ∧ Caller.RVMixedMemoryInputs data [] before ca oa cells ∧
      lower % 4 = 0 ∧ upper % 4 = 0 ∧ 2 ≤ lower ∧ lower ≤ upper ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVWindowScheduleSoundnessClaim` can be met, with a caller and a worker row in the
    window. -/
def Caller.RVWindowScheduleSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (addresses : List (BitVec 32)) (lower upper : Nat),
    Caller.RVRequestChecks data ∧ Caller.RVRequestInputs data before addresses ∧ lower % 4 = 0 ∧ upper % 4 = 0 ∧
      2 ≤ lower ∧ lower ≤ upper ∧ (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower ∧
      upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value ∧
      upper = lower + 4 * (data.workers.windowRows lower upper).length ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVMixedWindowProjectionSoundnessClaim` can be met, with a caller and a worker row in
    the window. -/
def Caller.RVMixedWindowProjectionSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell) (lower upper : Nat),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program before ca oa cells ∧
      lower % 4 = 0 ∧ upper % 4 = 0 ∧ 2 ≤ lower ∧ lower ≤ upper ∧
      (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower ∧
      upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value ∧
      upper = lower + 4 * (data.workers.windowRows lower upper).length ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVMixedWindowSequenceSoundnessClaim` can be met, with a caller and a worker row in the
    first window. -/
def Caller.RVMixedWindowSequenceSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell) (cut : Nat) (windows : List (Nat × Nat)),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program before ca oa cells ∧
      cut % 4 = 0 ∧ 2 ≤ cut ∧ Caller.WindowsOrdered cut windows ∧ data.callers ≠ [] ∧
      ∃ window ∈ windows, data.workers.windowRows window.1 window.2 ≠ []

/-- The assumptions of `Caller.RVCallerCyclesSoundnessClaim` can be met, with a caller. -/
def Caller.RVCallerCyclesSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (initial : RV.State) (ca oa : List (BitVec 32))
    (cells : List Trace.Cell),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program initial ca oa cells ∧
      0 < (Trace.timeOfPair data.machine.initial.timestamp).value ∧ data.callers ≠ []

/-- The assumptions of `Caller.RVControlPreparationSoundnessClaim` can be met, with a caller. -/
def Caller.RVControlPreparationSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell) (cut : Nat) (register : BitVec 5) (literal : Caller.ControlLiteral),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program before ca oa cells ∧
      Caller.RVControlPreparation data program cut register literal ∧ register ≠ 0 ∧ cut % 4 = 0 ∧
      data.callers ≠ []

/-- The assumptions of `Caller.RVControlPreparationWindowSoundnessClaim` can be met, with a caller and a worker row
    in the window. -/
def Caller.RVControlPreparationWindowSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State) (ca oa : List (BitVec 32)) (cells : List Trace.Cell) (lower upper : Nat) (firstRegister lastRegister : BitVec 5)
    (firstLiteral lastLiteral : Caller.ControlLiteral),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVMixedMemoryInputs data program before ca oa cells ∧
      Caller.RVControlPreparation data program lower firstRegister firstLiteral ∧
      Caller.RVControlPreparation data program upper lastRegister lastLiteral ∧ firstRegister ≠ 0 ∧
      lastRegister ≠ 0 ∧ lower % 4 = 0 ∧ upper % 4 = 0 ∧ lower ≤ upper ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVProgramWindowScheduleSoundnessClaim` can be met, with a caller and a worker row in
    the window. -/
def Caller.RVProgramWindowScheduleSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (program : List UnifiedReduced.RVProgramEntry) (before : RV.State)
    (ca oa : List (BitVec 32)) (family : Delegation.Family) (lower upper : Nat),
    Caller.RVMixedMemoryAccepted data program ∧ Caller.RVRequestInputs data before ca ∧
      Trace.rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program ∧
      Caller.RVSequentialProgram program ∧ Caller.RVProgramCallerRegion data program family lower upper ∧
      lower % 4 = 0 ∧ upper % 4 = 0 ∧ 2 ≤ lower ∧ lower ≤ upper ∧
      (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower ∧
      upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-! Non-vacuity of the complete-span caller claims: their assumptions can be met (with the reduced G span), with a
    selected caller and, for the window claims, worker rows in the window. -/

/-- The assumptions of `Caller.RVSharedSpanSoundnessClaim` can be met, with a caller. -/
def Caller.RVSharedSpanSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (addresses : List (BitVec 32))
    (cells : List Trace.Cell) (span : Delegation.Caller.HashSpan),
    Caller.RVMixedMemoryAccepted data [] ∧ Caller.RVSharedSpanInputs data before addresses cells span ∧
      data.callers ≠ []

/-- The assumptions of `Caller.RVRequestHashWindowSoundnessClaim` can be met, with a caller and worker rows in the
    window. -/
def Caller.RVRequestHashWindowSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (addresses : List (BitVec 32))
    (cells : List Trace.Cell) (span : Delegation.Caller.HashSpan) (lower upper : Nat),
    Caller.RVRequestChecks data ∧ Delegation.MemoryAccepted data.workers ∧ Caller.RVRequestInputs data before addresses ∧
      Delegation.Caller.HashSpan.RVRequestWindowInputs span data.workers before cells lower upper ∧
      (∀ cell ∈ cells, cell.Aligned) ∧ lower % 4 = 0 ∧ upper % 4 = 0 ∧ 2 ≤ lower ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVJointHashWindowSoundnessClaim` can be met, with a caller and worker rows in the
    window. -/
def Caller.RVJointHashWindowSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (addresses : List (BitVec 32))
    (cells : List Trace.Cell) (span : Delegation.Caller.HashSpan) (lower upper : Nat),
    Caller.RVMixedMemoryAccepted data [] ∧ Caller.RVJointHashWindowInputs data before addresses cells span lower upper ∧
      lower % 4 = 0 ∧ upper % 4 = 0 ∧ 2 ≤ lower ∧ lower ≤ upper ∧ data.callers ≠ [] ∧
      data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVPreparedHashWindowSoundnessClaim` can be met, with a caller and worker rows in the
    window. -/
def Caller.RVPreparedHashWindowSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (ca oa : List (BitVec 32))
    (cells : List Trace.Cell) (program : List UnifiedReduced.RVProgramEntry) (span : Delegation.Caller.HashSpan)
    (lower upper : Nat),
    Caller.RVMixedMemoryAccepted data program ∧
      Caller.RVPreparedHashWindowInputs data before ca oa cells program span lower upper ∧ lower % 4 = 0 ∧
      upper % 4 = 0 ∧ data.callers ≠ [] ∧ data.workers.windowRows lower upper ≠ []

/-- The assumptions of `Caller.RVPreparedHashSequenceSoundnessClaim` can be met, with a caller and worker rows in
    the first window. -/
def Caller.RVPreparedHashSequenceSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (ca oa : List (BitVec 32))
    (cells : List Trace.Cell) (program : List UnifiedReduced.RVProgramEntry) (first : Caller.HashWindow)
    (rest : List Caller.HashWindow),
    Caller.RVMixedMemoryAccepted data program ∧
      Caller.RVPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper ∧
      (∀ window ∈ rest, Caller.RVPreparedHashWindowInputs data before ca oa cells program
        window.span window.lower window.upper) ∧
      Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval) ∧ data.callers ≠ [] ∧
      data.workers.windowRows first.lower first.upper ≠ []

/-- The assumptions of `Caller.RVPreparedProtocolSequenceSoundnessClaim` can be met, with a caller and worker rows
    in the first window. -/
def Caller.RVPreparedProtocolSequenceSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (ca oa : List (BitVec 32))
    (cells : List Trace.Cell) (program : List UnifiedReduced.RVProgramEntry) (regions : List Caller.RoundRegion)
    (first : Caller.HashWindow) (rest : List Caller.HashWindow),
    Caller.RVMixedMemoryAccepted data program ∧
      Caller.RVPreparedProtocolInputs data before ca oa cells program regions ∧
      (∀ window ∈ first :: rest, Caller.RVPreparedProtocolWindowInputs data program window) ∧
      Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval) ∧ data.callers ≠ [] ∧
      data.workers.windowRows first.lower first.upper ≠ []

/-- The assumptions of `Caller.RVProgramPreparedProtocolSequenceSoundnessClaim` can be met, with a caller and
    worker rows in the first window. -/
def Caller.RVProgramPreparedProtocolSequenceSoundnessSatisfiableClaim : Prop :=
  ∃ (data : Caller.RVRequestTrace babyBearModulus) (before : RV.State) (ca oa : List (BitVec 32))
    (cells : List Trace.Cell) (program : List UnifiedReduced.RVProgramEntry) (regions : List Caller.RoundRegion)
    (first : Caller.HashWindow) (rest : List Caller.HashWindow),
    Caller.RVMixedMemoryAccepted data program ∧
      Caller.RVPreparedProtocolInputs data before ca oa cells program regions ∧
      Caller.RVSequentialProgram program ∧
      (∀ window ∈ first :: rest, Caller.RVProgramProtocolWindowInputs data program window) ∧
      Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval) ∧ data.callers ≠ [] ∧
      data.workers.windowRows first.lower first.upper ≠ []

end Airbender.UnifiedReduced
