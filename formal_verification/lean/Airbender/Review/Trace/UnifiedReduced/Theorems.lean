import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.SharedSpans
import Airbender.Proofs.UnifiedReduced.RequestWindows
import Airbender.Proofs.UnifiedReduced.MixedWindows
import Airbender.Proofs.UnifiedReduced.JointHashWindows
import Airbender.Proofs.UnifiedReduced.MixedWindowProjection
import Airbender.Proofs.UnifiedReduced.ControlPreparation
import Airbender.Proofs.UnifiedReduced.PreparedHashWindows
import Airbender.Proofs.UnifiedReduced.PreparedRoundWindows
import Airbender.Proofs.UnifiedReduced.CallerCycles
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
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
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
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
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
theorem Caller.shared_span_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell} {span : Delegation.Caller.HashSpan}
    (accepted : Caller.MixedMemoryAccepted data [])
    (inputs : Caller.SharedSpanInputs data before addresses cells span) :
    Caller.SharedSpanEffects data before cells span :=
  Caller.Proofs.shared_span_effects hp clockInverse accepted inputs

/-- Unified caller spans match the complete native worker rows between the
    same instruction-boundary cuts. Counts and unique native slots are derived;
    zero-clock surplus effects stay before the cut rather than being excluded. -/
theorem Caller.request_window_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper :=
  Caller.Proofs.request_windows hp clockInverse accepted inputs first last pastZero

/-- Unified caller requests and the complete hash reference bind the same native
    window. Public worker initialization, mode/count ABI and worker-only matching
    remain visible; caller control preparation and joint retirement are separate. -/
theorem Caller.request_hash_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (wordInverse : 64 * (-31457280 : ZMod p) = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
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
theorem Caller.mixed_window_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
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
theorem Caller.joint_hash_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.window_projection_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data []) (inputs : Caller.MixedMemoryInputs data [] before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper) :
    Caller.ProjectedWindowExecution data before cells lower upper :=
  Caller.Proofs.projected_window hp clockInverse rotationInverse accepted inputs first last positive ordered

/-- Accepted state matching counts every instruction between the public cuts.
    The four-tick duration and request matching derive a caller-only region
    without supplying selectors or an instruction schedule. -/
theorem Caller.window_schedule_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.mixed_window_projection_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
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
theorem Caller.control_preparation_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
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
theorem Caller.control_preparation_window_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
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
theorem Caller.mixed_window_chain_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
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
theorem Caller.mixed_window_sequence_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {cut : Nat} {windows : List (Nat × Nat)}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (first : cut % 4 = 0) (positive : 2 ≤ cut) (ordered : Caller.WindowsOrdered cut windows) :
    Caller.MixedWindowSequenceExecution data before cells cut windows :=
  Caller.Proofs.mixed_window_sequence hp clockInverse rotationInverse accepted inputs first positive ordered

/-- Complete G and Keccak references reach the actual mixed-history cut states
    after original public literal preparation. Shared matching derives controls,
    caller scheduling, worker boundaries and native reads. Other nonround workers
    may precede or follow the homogeneous selected span. Public span ABI,
    program/domain and modeled tables remain explicit; no worker masks are supplied. -/
theorem Caller.prepared_hash_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    Caller.JointHashWindowResult data before cells span lower upper :=
  Caller.Proofs.prepared_hash_window hp clockInverse accepted inputs first last

/-- Two complete prepared G/Keccak references compose through one continuous
    history, including the intervening preparation and other worker effects.
    Public mode/count/duration and nonround worker scope remain explicit. -/
theorem Caller.prepared_hash_chain_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {firstSpan secondSpan : Delegation.Caller.HashSpan} {a b c d : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (firstInputs : Caller.PreparedHashWindowInputs data before ca oa cells program firstSpan a b)
    (secondInputs : Caller.PreparedHashWindowInputs data before ca oa cells program secondSpan c d)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c) :
    Caller.PreparedHashChainResult data before cells firstSpan secondSpan a b c d :=
  Caller.Proofs.prepared_hash_chain hp clockInverse accepted firstInputs secondInputs aa ba ca' da gap

/-- A nonempty ordered list of complete prepared G/Keccak references shares one
    continuous actual memory history. Each span retains its public preparation,
    mode/count/duration and nonround scope; all intermediate states are derived. -/
theorem Caller.prepared_hash_sequence_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (firstInputs : Caller.PreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, Caller.PreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.prepared_hash_sequence hp clockInverse accepted firstInputs restInputs ordered

/-- Public LUI preparation and raw joint matching derive exclusive masks within
    one caller region. Its local ten-position bound remains explicit; earlier
    workers, including other families, remain outside the selected region. -/
theorem Caller.prepared_round_region_masks_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.prepared_protocol_sequence_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {regions : List Caller.RoundRegion} {first : Caller.HashWindow} {rest : List Caller.HashWindow}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedProtocolInputs data before ca oa cells program regions)
    (scopes : ∀ window ∈ first :: rest, Caller.PreparedProtocolWindowInputs data program window)
    (ordered : Caller.WindowsOrdered first.lower ((first :: rest).map Caller.HashWindow.interval)) :
    Caller.PreparedHashSequenceResult data before cells first rest :=
  Caller.Proofs.prepared_protocol_sequence hp clockInverse accepted inputs scopes ordered

/-- Public LUI preparation and native matching derive all extended-BLAKE masks
    before Sail transport. The public suffix duration and ten-position ABI remain explicit. -/
theorem Caller.prepared_round_masks_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {flags : Fin 8} {lower : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedRoundInputs data before ca oa cells program flags lower) (first : lower % 4 = 0) :
    ∀ row ∈ data.workers.rows, ∃ round, Blake2Round.Memory.RoundMask row.assignment round :=
  Caller.Proofs.prepared_round_masks hp clockInverse accepted inputs first

/-- Complete extended-BLAKE compression reaches the actual prepared mixed-history
    cut states. Controls, masks, caller selectors and worker boundaries are derived. -/
theorem Caller.prepared_round_window_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State}
    {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.ProgramEntry}
    {flags : Fin 8} {lower upper : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedRoundWindowInputs data before ca oa cells program flags lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    Caller.JointHashWindowResult data before cells (.blakeRound flags) lower upper :=
  Caller.Proofs.prepared_round_window hp clockInverse accepted inputs first last

/-- Actual caller fetch, issued-worker references and Sail PC retirement use
    one shared history. The physical/code domain and existing worker ABI remain explicit. -/
theorem Caller.caller_cycles_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (code : Caller.CodeProfile data program cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value) :
    Caller.CallerCycleEffects data program initial cells :=
  Caller.Proofs.caller_cycles accepted inputs code started

/-- The prepared extended-round scope derives masks before constructing the
    same actual caller cycles; no mask or intermediate state is supplied. -/
theorem Caller.prepared_round_cycles_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    {flags : Fin 8} {lower : Nat}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.PreparedRoundInputs data initial ca oa cells program flags lower) (first : lower % 4 = 0)
    (code : Caller.CodeProfile data program cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value) :
    Caller.CallerCycleEffects data program initial cells :=
  Caller.Proofs.prepared_round_caller_cycles accepted inputs first code started

/-- Public sequential code identifies a caller region; native matching derives
    its worker family, exact counts and slots without a supplied worker duration. -/
theorem Caller.program_window_schedule_soundness [Fact p.Prime]
    (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.wrapped_program_address_soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
    (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
    (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.program_round_live_masks_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
    (hp : 2 * Trace.timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.program_prepared_protocol_sequence_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.wrapped_program_window_schedule_soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.wrapped_program_round_region_soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.wrapped_program_prepared_protocol_sequence_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
theorem Caller.wrapped_program_round_live_masks_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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
    (hp : 4194304 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
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

end Airbender.UnifiedReduced
