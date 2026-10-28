import Airbender.Compatibility.UnifiedReduced
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.MixedCycleComposition
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.SharedSpans
import Airbender.Proofs.UnifiedReduced.RequestWindows
import Airbender.Proofs.UnifiedReduced.MixedWindows
import Airbender.Proofs.UnifiedReduced.JointHashWindows
import Airbender.Proofs.UnifiedReduced.MixedWindowProjection
import Airbender.Proofs.UnifiedReduced.ControlPreparation
import Airbender.Proofs.UnifiedReduced.PCRelativePreparation
import Airbender.Proofs.UnifiedReduced.RegisterPreparation
import Airbender.Proofs.UnifiedReduced.RegisterChains
import Airbender.Proofs.UnifiedReduced.RegisterDataflow
import Airbender.Proofs.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.UnifiedReduced.ComputedHashWindows
import Airbender.Proofs.UnifiedReduced.ComputedRoundRegions
import Airbender.Proofs.UnifiedReduced.PreparedRoundWindows
import Airbender.Proofs.UnifiedReduced.CallerCycles
import Airbender.Proofs.UnifiedReduced.UnissuedWorkers
import Airbender.Proofs.UnifiedReduced.WorkerExecution
import Airbender.Proofs.UnifiedReduced.Segmentation
import Airbender.Proofs.Delegation.RequestHashWindows

namespace Airbender.UnifiedReduced

/-- Standard instructions and project TRIADD/XORROT retire in one trace, with
    their original public Sail decoding and shared initialized history. Final
    PC/cells agree with native terminal tokens; readonly ROM uses actual public
    bytes rather than zero shadow slots. `Mixed.Inputs` contains only the shared
    public boot/configuration/profile conditions. No row reads, bounds, decoded
    results or expected outputs are assumptions. Delegation callers are outside
    this registry. -/
theorem Mixed.execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Mixed.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Mixed.Step program) trace initial cells (Trace.ROMView.token initial) :=
  Mixed.Proofs.trace_execution hp clockInverse byteInverse inputs accepted decoded

/-- Every admitted native row, in its history-derived order, executes the original
    Sail instruction fetched from public bytes. The final PC and all tracked
    cells match the declared terminal tokens; readonly ROM uses its public bytes.
    `ExecutionInputs` lists public boot/configuration/profile conditions. Reads,
    selectors and word bounds are proved internally from the imported artifact,
    modeled tables and logical matching. No terminal-PC normalization is needed. -/
theorem execution_soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : ExecutionInputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Step program) trace initial cells (Trace.ROMView.token initial) :=
  Proofs.trace_execution hp clockInverse byteInverse inputs accepted decoded

open Airbender.Reference.RiscV

/-- Unified standard/custom instructions, callers and workers share one public
    initialized architecture. Reads, word/address bounds, x0 values and worker
    references are derived through Clean history and actual Sail transfers.
    Whole retirement, native ROM shadows and hash spans remain separate. -/
theorem Caller.mixed_memory_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells) : Caller.MixedMemoryEffects data before cells :=
  Caller.Proofs.mixed_memory_effects accepted inputs

/-- Complete BLAKE G, extended BLAKE and Keccak spans reach their pinned
    references in one actual shared terminal state. The empty ordinary registry
    establishes caller-only rows. Public initialization, mode/span-size ABI,
    modeled tables and logical matching remain visible in `SharedSpanInputs`.
    Worker boundaries, all ranges and intermediate controls are derived.
    This is a memory-effect claim; PC retirement, arbitrary mixed-ISA span
    segmentation and unissued-worker exclusion remain separate. -/
theorem Caller.shared_span_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan}
    (accepted : Caller.MixedMemoryAccepted data [])
    (inputs : Caller.SharedSpanInputs data before addresses cells span) :
    Caller.SharedSpanEffects data before cells span :=
  Caller.Proofs.shared_span_effects hp clockInverse accepted inputs

/-- Unified caller spans match the complete native worker rows between the
    same instruction-boundary cuts. Counts and unique native slots are derived;
    zero-clock surplus effects stay before the cut rather than being excluded. -/
theorem Caller.request_window_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper :=
  Caller.Proofs.request_windows hp clockInverse accepted inputs first last pastZero

/-- Unified caller requests and the complete hash reference bind the same native
    window. Public worker initialization, mode/count ABI and worker-only matching
    remain visible; caller control preparation and joint retirement are separate. -/
theorem Caller.request_hash_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (wordInverse : SerializedInverse.Scale64 p)
    (byteInverse : SerializedInverse.Scale256 p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : Caller.RequestChecks data) (workers : Delegation.MemoryAccepted data.workers)
    (program : Caller.RequestInputs data before addresses)
    (inputs : span.RequestWindowInputs data.workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    span.RequestWindowResult data.callers data.workers before cells lower upper :=
  Delegation.Caller.Proofs.bind_hash_window hp wordInverse byteInverse workers inputs aligned
    (Caller.Proofs.request_windows (by norm_num [Trace.timestampBase]; omega) clockInverse
      accepted program first last pastZero)

/-- Complete instruction and worker rows between public aligned cuts execute
    in one initialized architectural history. Actual cut states, canonical words,
    retained timestamps and request slots are derived from joint matching.
    This is memory transport; whole caller retirement and hash ABI remain separate. -/
theorem Caller.mixed_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0)
    (pastZero : 2 ≤ lower) (ordered : lower ≤ upper) :
    Caller.MixedWindowExecution data before cells lower upper :=
  Caller.Proofs.mixed_window_execution hp clockInverse rotationInverse accepted inputs first last pastZero ordered

/-- Caller-only hash windows reach their complete pinned reference at the
    actual joint cut states. Shared matching derives worker boundaries, entry
    controls and round masks. Public mode/count, prefix scope and modeled tables
    remain explicit; ordinary control preparation and ISA retirement are separate. -/
theorem Caller.joint_hash_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data [])
    (inputs : Caller.JointHashWindowInputs data before addresses cells span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) :
    Caller.JointHashWindowResult data before cells span lower upper :=
  Caller.Proofs.joint_hash_window hp clockInverse accepted inputs first last positive ordered

/-- Projected worker memory retains the joint states and native timestamps.
    The empty ordinary registry derives caller-only rows; no independent worker
    matching or boundary values are supplied. -/
theorem Caller.window_projection_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data []) (inputs : Caller.MixedMemoryInputs data [] before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) :
    Caller.ProjectedWindowExecution data before cells lower upper :=
  Caller.Proofs.projected_window hp clockInverse rotationInverse accepted inputs first last positive ordered

/-- Accepted state matching counts every instruction between the public cuts.
    The four-tick duration and request matching derive a caller-only region
    without supplying selectors or an instruction schedule. -/
theorem Caller.window_schedule_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value)
    (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length) :
    Caller.CallerWindowSchedule data lower upper :=
  Caller.Proofs.caller_window_schedule hp clockInverse accepted inputs first last positive ordered afterInitial beforeTerminal duration

/-- Caller regions within mixed history derive worker matching and retained
    boundary images at the actual cut states. Earlier ordinary effects remain
    in the joint prefix; complete hash entry protocols and retirement are separate. -/
theorem Caller.mixed_window_projection_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value)
    (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length) :
    Caller.MixedProjectedWindowExecution data before cells lower upper :=
  Caller.Proofs.mixed_projected_window hp clockInverse rotationInverse accepted inputs
    first last positive ordered afterInitial beforeTerminal duration

/-- Original public ADDI-from-x0/LUI decoding and accepted native writes prepare
    the actual control at the prepared cut, retaining earlier worker effects.
    Public literal, arithmetic or sequential registries admit successive preparations.
    Native PC/clock matching identifies the literal row; its timestamp survives. Program and final-cycle scope
    remain explicit, with no desired control read or row selector as an input. -/
theorem Caller.control_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {register : BitVec 5} {literal : Caller.ControlLiteral}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (scope : Caller.ControlPreparation data program cut register literal)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    Caller.PreparedBoundaryExecution data before cells cut register literal :=
  Caller.Proofs.control_preparation hp clockInverse rotationInverse accepted inputs scope nonzero aligned

/-- Two prepared controls use the same actual states and intervening native
    history. Decoding, matching and public preparation cuts derive both controls. -/
theorem Caller.control_preparation_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {lower upper : Nat} {firstRegister lastRegister : BitVec 5}
    {firstLiteral lastLiteral : Caller.ControlLiteral}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (firstScope : Caller.ControlPreparation data program lower firstRegister firstLiteral)
    (lastScope : Caller.ControlPreparation data program upper lastRegister lastLiteral)
    (firstNonzero : firstRegister ≠ 0) (lastNonzero : lastRegister ≠ 0)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper) :
    Caller.PreparedControlWindow data before cells lower upper firstRegister firstLiteral lastRegister lastLiteral :=
  Caller.Proofs.control_preparation_window hp clockInverse rotationInverse accepted inputs
    firstScope lastScope firstNonzero lastNonzero first last ordered

/-- Two native windows and their intervening gap form one actual memory execution
    from public initialization. Every cut state and retained boundary is derived. -/
theorem Caller.mixed_window_chain_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {a b c d : Nat} (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0)
    (positive : 2 ≤ a) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d) :
    Caller.MixedWindowChainExecution data before cells a b c d :=
  Caller.Proofs.mixed_window_chain hp clockInverse rotationInverse accepted inputs aa ba ca' da positive ab bc cd

/-- An ordered finite list of native windows and gaps executes continuously
    from public initialization. Matching derives every actual boundary and clock;
    instruction retirement and protocol shape remain separate. -/
theorem Caller.mixed_window_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {windows : List (Nat × Nat)}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (first : cut % 4 = 0) (positive : 2 ≤ cut) (ordered : Caller.WindowsOrdered cut windows) :
    Caller.MixedWindowSequenceExecution data before cells cut windows :=
  Caller.Proofs.mixed_window_sequence hp clockInverse rotationInverse accepted inputs first positive ordered

/-- Public LUI preparation and raw joint matching derive exclusive masks within
    one caller region. Its local ten-position bound remains explicit; earlier
    workers, including other families, remain outside the selected region. -/
theorem Caller.prepared_round_region_masks_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion} {region : Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedProtocolInputs data before ca oa cells program regions)
    (scope : Caller.RoundRegionInputs data program region) :
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round :=
  Caller.Proofs.prepared_round_region_masks hp clockInverse accepted inputs.toProtocolContextInputs scope

/-- Complete prepared G, extended-BLAKE and Keccak lists share one continuous
    actual memory execution. Every extended-round worker must belong to an
    explicit prepared controller region; raw matching derives its mask first.
    Public preparation/protocol shape stays visible, with whole retirement separate. -/
theorem Caller.prepared_protocol_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.PreparedProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.prepared_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Strict native memory order and alignment derive positive caller clocks.
    Actual fetch, matched worker effects and PC retirement therefore share one
    history without an extra positive initial-clock premise. Surplus zero-clock
    workers remain in its prefix; full custom-CSR ABI stays separate. -/
theorem Caller.native_caller_cycles_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (code : Caller.CodeProfile data program cells) :
    Caller.CallerCycleEffects data program initial cells :=
  Caller.Proofs.native_caller_cycles accepted inputs code

/-- Public sequential code identifies a caller region; native matching derives
    its worker family, exact counts and slots without a supplied worker duration. -/
theorem Caller.program_window_schedule_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)}
    {family : Delegation.Family} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.SequentialProgram program)
    (region : Caller.ProgramCallerRegion data program family lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) :
    Caller.ProgramCallerWindow data family lower upper :=
  Caller.Proofs.program_caller_window hp clockInverse accepted publicProgram ordinaryProgram registry region
    first last positive ordered afterInitial beforeTerminal

/-- Public sequential/comparison decoding and native state matching derive RV32
    program addresses from clocks, including comparison PC wraparound. Public
    code alignment, modeled setup and comparison field compatibility stay explicit. -/
theorem Caller.wrapped_program_address_soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before state : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry}
    (setup : data.machine.rom = Setup.table state) (accepted : Caller.MixedMemoryAccepted data program)
    (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (registry : Caller.WrappedSequentialProgram program) :
    ∀ row ∈ data.machine.rows, row.start.word.toBitVec = data.machine.initial.word.toBitVec +
      BitVec.ofNat 32 (Delegation.Caller.startClock row - (Trace.timeOfPair data.machine.initial.timestamp).value) :=
  Caller.Proofs.wrapped_program_pc_clock hp clockInverse setup accepted publicProgram ordinaryProgram registry

/-- Public code and an extent of at most forty ticks derive this prepared
    controller's worker family, ten-position bound and exact four-tick duration. -/
theorem Caller.program_round_region_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {region : Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.SequentialProgram program)
    (scope : Caller.ProgramRoundRegionInputs data program region) :
    Caller.RoundRegionInputs data program region :=
  Caller.Proofs.program_round_region_inputs hp clockInverse accepted publicProgram ordinaryProgram registry scope

/-- Public decoded round CSR coverage derives membership for every live round
    worker. Membership is equivalent to live invocation; zero-clock surplus
    workers remain outside these prepared regions, with all their effects retained. -/
theorem Caller.program_round_coverage_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.SequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.ProgramRoundRegionInputs data program region)
    (coverage : Caller.ProgramRoundCallerCoverage data regions) : Caller.RoundWorkerCoverage data regions :=
  Caller.Proofs.program_round_worker_coverage hp clockInverse accepted publicProgram ordinaryProgram registry scopes coverage

/-- Public code coverage and LUI preparation derive exclusive masks for every
    issued extended-round worker from raw matching. Global worker coverage and
    mask behavior of zero-clock surplus round workers remain separate. -/
theorem Caller.program_round_live_masks_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProtocolContextInputs data before ca oa cells program)
    (registry : Caller.SequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.ProgramRoundRegionInputs data program region)
    (coverage : Caller.ProgramRoundCallerCoverage data regions) :
    ∀ worker ∈ data.workers.rows, worker.family = Delegation.Family.blakeRound →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ round, Blake2Round.Memory.RoundMask worker.assignment round :=
  Caller.Proofs.program_round_live_masks hp clockInverse accepted inputs registry scopes coverage

/-- With public round CSR coverage, full worker coverage holds exactly when
    no zero-clock extended-round worker is present. This is a proved boundary,
    not a nonzero-invocation assumption or a general exclusion of surplus workers. -/
theorem Caller.program_round_global_coverage_boundary_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.SequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.ProgramRoundRegionInputs data program region)
    (coverage : Caller.ProgramRoundCallerCoverage data regions) :
    (∀ worker ∈ data.workers.rows, worker.family = Delegation.Family.blakeRound →
      ∃ region ∈ regions, worker ∈ data.workers.windowRows region.lower region.upper) ↔
    ¬ ∃ worker ∈ data.workers.rows, worker.family = Delegation.Family.blakeRound ∧
      (Delegation.Requests.fulfillment worker).time = (0, 0) :=
  Caller.Proofs.round_worker_coverage_boundary
    (Caller.program_round_coverage_soundness hp clockInverse accepted publicProgram ordinaryProgram registry scopes coverage)

/-- Public caller regions derive selected span and controller families/counts
    before all three references compose in one continuous prepared history.
    Global controller coverage, public preparation/extents and matching stay explicit. -/
theorem Caller.program_prepared_protocol_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProgramPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.ProgramProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.program_prepared_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Public modular code regions and accepted matching derive selected callers,
    worker families, exact counts and slots through comparison PC wraparound. -/
theorem Caller.wrapped_program_window_schedule_soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before state : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)}
    {family : Delegation.Family} {lower upper : Nat}
    (setup : data.machine.rom = Setup.table state)
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.WrappedSequentialProgram program)
    (region : Caller.WrappedProgramCallerRegion data program family lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (Trace.timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) :
    Caller.ProgramCallerWindow data family lower upper :=
  Caller.Proofs.wrapped_program_caller_window hp clockInverse setup accepted publicProgram ordinaryProgram registry region
    first last positive ordered afterInitial beforeTerminal

/-- Modular public code and an extent of at most forty ticks derive local
    round-controller family/count/duration before the existing mask transport. -/
theorem Caller.wrapped_program_round_region_soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {region : Caller.RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.WrappedSequentialProgram program)
    (scope : Caller.WrappedProgramRoundRegionInputs data program region) :
    Caller.RoundRegionInputs data program region :=
  Caller.Proofs.wrapped_program_round_region_inputs hp clockInverse setup accepted publicProgram ordinaryProgram registry scope

/-- Complete references compose continuously after selected span/controller shape
    is derived from modular public regions. Global round-worker coverage remains
    explicit; unissued effects are retained, with whole caller retirement separate. -/
theorem Caller.wrapped_program_prepared_protocol_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.WrappedProgramPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.WrappedProgramProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.wrapped_program_prepared_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Public modular round-CSR occurrence coverage derives membership for every live round
    worker. Membership is equivalent to live invocation; zero-clock surplus
    workers remain outside these prepared regions, with all their effects retained. -/
theorem Caller.wrapped_program_round_coverage_soundness [Fact p.Prime]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.WrappedProgramRoundRegionInputs data program region)
    (coverage : Caller.WrappedProgramRoundCallerCoverage data regions) : Caller.RoundWorkerCoverage data regions :=
  Caller.Proofs.wrapped_program_round_worker_coverage hp clockInverse setup accepted publicProgram ordinaryProgram registry scopes coverage

/-- Modular public code coverage and LUI preparation derive exclusive masks for every
    issued extended-round worker from raw matching. Global worker coverage and
    mask behavior of zero-clock surplus round workers remain separate. -/
theorem Caller.wrapped_program_round_live_masks_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProtocolContextInputs data before ca oa cells program)
    (registry : Caller.WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.WrappedProgramRoundRegionInputs data program region)
    (coverage : Caller.WrappedProgramRoundCallerCoverage data regions) :
    ∀ worker ∈ data.workers.rows, worker.family = Delegation.Family.blakeRound →
      Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      ∃ round, Blake2Round.Memory.RoundMask worker.assignment round :=
  Caller.Proofs.wrapped_program_round_live_masks hp clockInverse accepted inputs registry scopes coverage

/-- With public round CSR coverage, full worker coverage holds exactly when
    no zero-clock extended-round worker is present. This is a proved boundary,
    not a nonzero-invocation assumption or a general exclusion of surplus workers. -/
theorem Caller.wrapped_program_round_global_coverage_boundary_soundness [Fact p.Prime]
    (hp : FieldCapacity.NativeRomCapacity p) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {regions : List Caller.RoundRegion}
    (setup : data.machine.rom = Setup.table before)
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.WrappedProgramRoundRegionInputs data program region)
    (coverage : Caller.WrappedProgramRoundCallerCoverage data regions) :
    (∀ worker ∈ data.workers.rows, worker.family = Delegation.Family.blakeRound →
      ∃ region ∈ regions, worker ∈ data.workers.windowRows region.lower region.upper) ↔
    ¬ ∃ worker ∈ data.workers.rows, worker.family = Delegation.Family.blakeRound ∧
      (Delegation.Requests.fulfillment worker).time = (0, 0) :=
  Caller.Proofs.round_worker_coverage_boundary
    (Caller.wrapped_program_round_coverage_soundness hp clockInverse setup accepted publicProgram ordinaryProgram registry scopes coverage)

/-- Every zero-clock worker reads the full public initialization tokens.
    Native clocks and architectural matching derive their origin and word bounds;
    all unissued writes and their later prefix effects remain admitted. -/
theorem Caller.unissued_worker_reads_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (image : Trace.initialImage before cells = some data.machine.initialMemory)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    (zero : (Delegation.Requests.fulfillment worker).time = (0, 0)) :
    Caller.InitialWorkerReads before cells worker :=
  Caller.Proofs.unissued_initial_reads hp clockInverse accepted publicProgram image member zero

/-- The actual public x12 seed characterizes every supported exclusive mask of
    an unissued extended-round worker. No supported-control, exclusive-mask or
    nonzero-invocation premise supplies the missing global coverage boundary. -/
theorem Caller.unissued_round_control_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (image : Trace.initialImage before cells = some data.machine.initialMemory)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) (family : worker.family = .blakeRound)
    (zero : (Delegation.Requests.fulfillment worker).time = (0, 0)) :
    Caller.InitialRoundControl before worker :=
  Caller.Proofs.unissued_round_initial_control hp clockInverse accepted publicProgram image member family zero

/-- The shared x10 access and initialized architectural matching distinguish
    invocation clocks across all four families, including zero. The unissued
    sublist has at most one occurrence; its effects remain in the actual history. -/
theorem Caller.worker_invocation_uniqueness_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (image : Trace.initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Trace.Cell.addressCode).Nodup) : Caller.WorkerInvocationUniqueness data :=
  Caller.Proofs.worker_invocation_uniqueness hp clockInverse accepted publicProgram image distinct

/-- All native workers have actual pre/post-states in one initialized execution.
    A zero-clock worker is its first group and observes the original public seed;
    later machine/worker effects and shared terminal cells remain connected.
    Every machine cycle is derived without an extra positive initial clock.
    Existing modeled-table and extended-round-mask inputs stay explicit. -/
theorem Caller.all_worker_execution_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells) :
    Caller.MixedWorkerExecution data before cells :=
  Caller.Proofs.mixed_worker_execution_effects accepted inputs

/-- AUIPC computes the prepared control from its derived public PC and immediate.
    Native constraints and matching derive its canonical cut token and timestamp;
    the same initialized history supplies the actual cut state. Earlier worker
    effects remain, with modeled tables and round ABI explicit. -/
theorem Caller.pc_relative_control_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p) (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {register : BitVec 5} {immediate : BitVec 20}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (scope : Caller.PCRelativePreparation data program cut register immediate)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    Caller.PCRelativePreparedBoundaryExecution data before cells cut register immediate :=
  Caller.Proofs.pc_relative_control_preparation hp clockInverse rotationInverse accepted inputs scope nonzero aligned

/-- Public register preparation instructions derive the actual protocol
    entry control and retain its native timestamp in the initialized history.
    Placement/dataflow conditions concern decoded code, with no supplied control read. -/
theorem Caller.hash_control_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p) (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {span : Delegation.Caller.HashSpan}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (source : Caller.HashControlPreparation data program cut span) (aligned : cut % 4 = 0) :
    Caller.PreparedBoundaryExecution data before cells cut span.controlRegister (Caller.hashPreparation span) :=
  Caller.Proofs.hash_control_preparation hp clockInverse rotationInverse accepted inputs source aligned

/-- Public register preparation reaches a complete selected G or
    Keccak reference at the actual joint cut states. Counts/duration, family,
    domain, modeled tables and logical matching stay explicit. -/
theorem Caller.computed_prepared_hash_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ComputedPreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    Caller.JointHashWindowResult data before cells span lower upper :=
  Caller.Proofs.computed_hash_window hp clockInverse accepted inputs first last

/-- A nonempty ordered list may mix all public preparation forms. Every gap
    and complete G/Keccak reference shares one continuously initialized history;
    intermediate states and protocol entry reads are derived. -/
theorem Caller.computed_prepared_hash_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (firstInputs : Caller.ComputedPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, Caller.ComputedPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.computed_hash_sequence hp clockInverse accepted firstInputs restInputs ordered

/-- Literal or AUIPC preparation and public modular code derive the selected
    caller/worker shape and exact native request slots, even for an empty region.
    No complete reference duration or worker-count premise is needed here. -/
theorem Caller.hash_prepared_public_window_schedule_soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (setup : data.machine.rom = Setup.table before)
    (accepted : Caller.MixedMemoryAccepted data program) (publicProgram : Caller.RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : Caller.WrappedSequentialProgram program)
    (source : Caller.HashControlPreparation data program lower span)
    (region : Caller.WrappedProgramCallerRegion data program span.family lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper)
    (beforeTerminal : upper ≤ (Trace.timeOfPair data.machine.terminal.timestamp).value) :
    Caller.ProgramCallerWindow data span.family lower upper :=
  Caller.Proofs.wrapped_program_hash_preparation_schedule hp clockInverse setup accepted publicProgram
    ordinaryProgram registry source region first last ordered beforeTerminal

/-- Complete selected G/Keccak references derive their caller/worker family,
    count and slots from public modular regions, then use public register
    preparation at the actual joint states. Public duration and nonround scope,
    domain, setup/tables and logical matching remain explicit. -/
theorem Caller.wrapped_program_computed_hash_window_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {window : Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.WrappedProgramComputedHashInputs data before ca oa cells program)
    (scope : Caller.WrappedProgramComputedHashWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    Caller.ProgramCallerWindow data window.span.family window.lower window.upper ∧
      Caller.JointHashWindowResult data before cells window.span window.lower window.upper :=
  Caller.Proofs.wrapped_program_computed_hash_window hp clockInverse accepted inputs scope first last

/-- A nonempty ordered list may mix all public preparation forms. Public
    modular regions derive all selected shapes; existing composition retains
    every gap and reference in one continuously initialized history. -/
theorem Caller.wrapped_program_computed_hash_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.WrappedProgramComputedHashInputs data before ca oa cells program)
    (scopes : ∀ window ∈ first :: rest, Caller.WrappedProgramComputedHashWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.wrapped_program_computed_hash_sequence hp clockInverse accepted inputs scopes ordered

/-- Literal or AUIPC preparation supplies the actual regional round-zero token.
    Raw initialized matching derives every selected round mask. Earlier workers
    remain in the prefix and global round coverage is not assumed. -/
theorem Caller.computed_round_region_masks_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {region : Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProtocolContextInputs data before ca oa cells program)
    (scope : Caller.ComputedRoundRegionInputs data program region) :
    ∀ row ∈ data.workers.windowRows region.lower region.upper,
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round :=
  Caller.Proofs.computed_round_region_masks hp clockInverse accepted inputs scope

/-- Public modular code and a forty-tick extent derive controller shape; either
    public preparation source and raw matching then derive its round masks. -/
theorem Caller.wrapped_program_computed_round_region_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {region : Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProtocolContextInputs data before ca oa cells program)
    (registry : Caller.WrappedSequentialProgram program)
    (scope : Caller.WrappedProgramComputedRoundRegionInputs data program region) :
    Caller.ComputedRoundRegionInputs data program region ∧
      ∀ row ∈ data.workers.windowRows region.lower region.upper,
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round :=
  Caller.Proofs.wrapped_program_computed_round_region_masks hp clockInverse accepted inputs registry scope

/-- Global source-aware mask transport retains the existing explicit coverage
    of every round worker by a prepared region, including its unissued boundary.
    No mask or control read is supplied. Domain/setup/tables remain explicit. -/
theorem Caller.computed_protocol_memory_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {regions : List Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ComputedPreparedProtocolInputs data before ca oa cells program regions) :
    Caller.MixedMemoryInputs data program before ca oa cells :=
  Caller.Proofs.computed_protocol_memory_inputs hp clockInverse accepted inputs

/-- Public modular round-CSR occurrences derive precisely live regional
    membership and every issued mask with either preparation source. Full
    coverage is equivalent to absence of zero-clock round workers; it is not
    assumed, and the unissued boundary remains explicit. -/
theorem Caller.wrapped_program_computed_round_coverage_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {regions : List Caller.RoundRegion}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProtocolContextInputs data before ca oa cells program)
    (registry : Caller.WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, Caller.WrappedProgramComputedRoundRegionInputs data program region)
    (coverage : Caller.WrappedProgramRoundCallerCoverage data regions) :
    Caller.RoundWorkerCoverage data regions ∧
      (∀ worker ∈ data.workers.rows, worker.family = .blakeRound →
        Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
        ∃ round, Blake2Round.Memory.RoundMask worker.assignment round) ∧
      ((∀ worker ∈ data.workers.rows, worker.family = .blakeRound →
          ∃ region ∈ regions, worker ∈ data.workers.windowRows region.lower region.upper) ↔
        ¬ ∃ worker ∈ data.workers.rows, worker.family = .blakeRound ∧
          (Delegation.Requests.fulfillment worker).time = (0, 0)) := by
  have covered := Caller.Proofs.wrapped_program_computed_round_worker_coverage (by omega) clockInverse
    inputs.setup accepted inputs.publicProgram inputs.ordinaryProgram registry scopes coverage
  exact ⟨covered, Caller.Proofs.wrapped_program_computed_round_live_masks hp clockInverse accepted inputs registry scopes coverage,
    Caller.Proofs.round_worker_coverage_boundary covered⟩

/-- Complete G, extended-BLAKE and Keccak references may mix all public
    preparation forms. Every gap and boundary state comes from one initialized history.
    Raw regional matching derives masks; full round-worker coverage stays explicit. -/
theorem Caller.computed_prepared_protocol_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.ComputedProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.computed_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Public modular caller/controller regions derive shape for every selected
    reference and controller. Each preparation source reaches complete G,
    extended-BLAKE and Keccak references in one continuously initialized history.
    Domain/setup/tables and full round-worker coverage remain explicit. -/
theorem Caller.wrapped_program_computed_protocol_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.WrappedProgramComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.WrappedProgramComputedProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.wrapped_program_computed_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Public register-dependent ADDI preparation derives its operand from the
    actual initialized cycle state, its RV32 result and canonical output token
    at cut minus two. Earlier issued/unissued effects and aliases are retained.
    No source read, operand bound, selector or desired result is supplied.
    Unrestricted public dataflow and complete Sail retirement remain separate. -/
theorem Caller.register_immediate_control_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {source register : BitVec 5} {immediate : BitVec 12}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (scope : Caller.RegisterImmediatePreparation data program cut source register immediate)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    Caller.RegisterImmediatePreparedBoundaryExecution data before cells cut source register immediate :=
  Caller.Proofs.register_immediate_control_preparation hp clockInverse rotationInverse accepted inputs scope nonzero aligned

/-- Finite public literal/AUIPC→ADDI chains derive each native source read and
    result through initialized matching, including changes of register and
    aliases. No intermediate state, expected operand or bound is supplied.
    Only selected preparation cycles are worker-free; earlier effects remain. -/
theorem Caller.register_chain_control_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (preparation : Caller.PublicRegisterPreparation data program cut register value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    Caller.RegisterChainPreparedBoundaryExecution data before cells cut register value :=
  Caller.Proofs.public_register_control_preparation hp clockInverse rotationInverse accepted inputs preparation nonzero aligned

/-- Public ADDIs to other GPRs may intervene between dataflow writes, including
    readonly refreshes of the tracked register. Initialized matching derives its
    value and actual token timestamp, retaining every gap write and prior effect. -/
theorem Caller.register_dataflow_control_preparation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (preparation : Caller.PublicRegisterDataflow data program cut register value)
    (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    Caller.RegisterDataflowBoundaryExecution data before cells cut register value :=
  Caller.Proofs.public_register_dataflow_control_preparation hp clockInverse rotationInverse accepted inputs preparation nonzero aligned

/-- Public caller code and initialized matching derive the actual canonical
    bigint return bit and its retained worker timestamp. Incoming control
    validity and whole custom-CSR retirement remain separate. -/
theorem Caller.bigint_control_boundary_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    (rotationInverse : SerializedInverse.Scale64 p)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {cut : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (scope : Caller.CallerControlPreparation data program .bigint cut) (aligned : cut % 4 = 0) :
    Caller.BigintControlBoundaryExecution data before cells cut :=
  Caller.Proofs.bigint_control_boundary_execution hp clockInverse rotationInverse accepted inputs scope aligned

/-- Public CSR occurrence coverage and ordered complete-protocol windows derive
    an exact partition of all issued hash requests. Zero-clock workers stay as
    explicit residuals; bigint callers and ordinary instructions may lie in gaps. -/
theorem Caller.hash_segmentation_soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)}
    {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry} {windows : List Caller.HashWindow} {cut : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.ProtocolContextInputs data before ca oa cells program) (registry : Caller.WrappedSequentialProgram program)
    (scopes : ∀ window ∈ windows, Caller.WrappedProgramComputedProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered cut (windows.map Caller.HashWindow.interval))
    (coverage : Caller.ProgramHashCallerCoverage data windows) : Caller.IssuedHashSegmentation data windows :=
  Caller.Proofs.program_hash_segmentation hp clockInverse accepted inputs registry scopes ordered coverage

/-- Every issued hash request belongs to exactly one complete selected reference
    in the same initialized history. Public code/protocol scope, modeled tables
    and the existing global extended-round mask boundary remain explicit. -/
theorem Caller.segmented_hash_sequence_soundness [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.WrappedProgramComputedPreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.WrappedProgramComputedProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval))
    (coverage : Caller.ProgramHashCallerCoverage data (first :: rest)) :
    Caller.SegmentedHashSequenceResult data before cells first rest :=
  Caller.Proofs.segmented_hash_sequence hp clockInverse accepted inputs scopes ordered coverage

end Airbender.UnifiedReduced

namespace Airbender.UnifiedReduced

/-- All ordinary retirement, caller observations and worker effects use one
    initialized history and the complete native PC/clock path. Terminal cells
    agree in its final retired-PC view. Public configuration, code/data domain,
    modeled tables and logical matching remain explicit. Callers satisfy the
    existing observation contract, not full custom-CSR reference execution;
    zero-clock residuals and invalid bigint controls remain exposed. -/
theorem Caller.mixed_cycle_soundness
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (profile : Caller.RetirementProfile data program initial cells) :
    Caller.MixedCycleEffects data program initial cells :=
  Caller.Proofs.mixed_cycle_effects accepted inputs profile

end Airbender.UnifiedReduced
