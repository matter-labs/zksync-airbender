import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.UnifiedReduced.ComputedHashWindows
import Airbender.Proofs.UnifiedReduced.HashPreparation
import Airbender.Proofs.Delegation.SpanTarget
import Airbender.Proofs.UnifiedReduced.RegisterDataflow

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- The existing public cell domain derives seed uniqueness for literal→ADDI;
    the only value equation is between public instruction constants. -/
theorem literal_addi_hash_preparation_source [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {cells : List Cell} {cut : Nat} {span : Delegation.Caller.HashSpan}
    {source : BitVec 5} {literal : ControlLiteral} {immediate : BitVec 12}
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (seed : ControlPreparation data program (cut - 4) source literal)
    (step : RegisterImmediatePreparation data program cut source span.controlRegister immediate)
    (nonzero : source ≠ 0)
    (value : registerImmediateValue literal.value immediate = span.controlStart) :
    HashControlPreparation data program cut span := by
  exact .literalAddi source literal immediate ⟨seed, step, nonzero, by
    rw [image_addresses initialization]
    exact distinct⟩ value

/-- Public initialization supplies the domain boundary for an arbitrarily long
    finite register chain. Its final equation concerns the public expression. -/
theorem register_chain_hash_preparation_source [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {cells : List Cell} {cut : Nat} {span : Delegation.Caller.HashSpan} {value : BitVec 32}
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (preparation : PublicRegisterPreparation data program cut span.controlRegister value)
    (entry : value = span.controlStart) : HashControlPreparation data program cut span := by
  exact .registerChain value preparation (by
    rw [image_addresses initialization]
    exact distinct) entry

/-- A final public ADDI consumes derived dataflow across unrelated writes.
    The existing public domain supplies uniqueness; the entry equation concerns
    only the public instruction expression. -/
theorem register_dataflow_hash_preparation_source [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {cells : List Cell} {cut : Nat} {span : Delegation.Caller.HashSpan}
    {source : BitVec 5} {value : BitVec 32} {immediate : BitVec 12}
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (prior : PublicRegisterDataflow data program (cut - 4) source value)
    (scope : RegisterImmediatePreparation data program cut source span.controlRegister immediate)
    (nonzero : source ≠ 0)
    (entry : registerImmediateValue value immediate = span.controlStart) :
    HashControlPreparation data program cut span := by
  exact .dataflowAddi source value immediate prior scope nonzero (by
    rw [image_addresses initialization]
    exact distinct) entry

theorem hash_control_preparation_after_initial [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {cut : Nat}
    {span : Delegation.Caller.HashSpan} (source : HashControlPreparation data program cut span) :
    (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut := by
  cases source with
  | literal scope => exact scope.afterInitial
  | pcRelative _ scope _ => exact scope.afterInitial
  | literalAddi _ _ _ scope _ => exact scope.step.afterInitial
  | registerChain _ preparation _ _ => exact public_register_preparation_after_initial preparation
  | dataflowAddi _ _ _ _ scope _ _ _ => exact scope.afterInitial

/-- The public placement condition is applied to the actual decoded instruction,
    whose membership and address are derived from native constraints and clocks. -/
theorem pc_relative_hash_control [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {span : Delegation.Caller.HashSpan} {immediate : BitVec 20}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PCRelativePreparation data program cut span.controlRegister immediate)
    (placement : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
      entry.pc + (immediate ++ (0 : BitVec 12)) = span.controlStart)
    (aligned : cut % 4 = 0) : pcRelativeControl data cut immediate = span.controlStart := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨row, member, last, ordinary⟩ := preparation_cycle_row size inverse accepted.toRequestChecks publicProgram
    scope.prefixScope scope.afterInitial scope.beforeTerminal aligned
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded row member ordinary)
  have address := (pc_relative_preparation_entry (by omega) inverse setup accepted publicProgram ordinaryProgram
    scope member last present query).1
  simpa only [pcRelativeControl, address] using placement entry present address

/-- Each public preparation form produces the canonical native entry token.
    Its actual write timestamp is retained before any hash-reference transport. -/
theorem hash_control_preparation_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {span : Delegation.Caller.HashSpan}
    {tokens : List (MemoryToken p)}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (source : HashControlPreparation data program cut span) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register span.controlRegister).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec span.controlStart := by
  cases source with
  | literal scope =>
    simpa only [hash_preparation_value] using preparation_token hp inverse accepted publicProgram ordinaryProgram
      initialization scope (hash_control_register_nonzero span) aligned matching
  | pcRelative immediate scope placement =>
    have value := pc_relative_hash_control hp inverse setup accepted publicProgram ordinaryProgram scope placement aligned
    simpa only [value] using pc_relative_preparation_token hp inverse setup accepted publicProgram ordinaryProgram
      initialization scope (hash_control_register_nonzero span) aligned matching
  | literalAddi source literal immediate scope value =>
    simpa only [value] using literal_addi_preparation_token hp inverse setup accepted publicProgram ordinaryProgram
      initialization scope (hash_control_register_nonzero span) aligned matching
  | registerChain value preparation unique entry =>
    simpa only [entry] using public_register_preparation_token hp inverse setup accepted publicProgram ordinaryProgram
      initialization unique preparation (hash_control_register_nonzero span) aligned matching
  | dataflowAddi source value immediate prior scope nonzero unique entry =>
    simpa only [entry] using register_immediate_preparation_token_of_value hp inverse setup accepted publicProgram ordinaryProgram
      initialization scope unique (public_register_dataflow_after_initial prior)
      (fun _ prefixMatching => public_register_dataflow_token hp inverse setup accepted publicProgram ordinaryProgram
        initialization unique prior nonzero (by have floor := public_register_dataflow_after_initial prior; omega) prefixMatching)
      (hash_control_register_nonzero span) aligned matching

theorem hash_control_preparation_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {span : Delegation.Caller.HashSpan}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (source : HashControlPreparation data program cut span) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) (boundary : NativeBoundary tokens atCut cells) :
    PreparedControl tokens atCut cut span.controlRegister (hashPreparation span) := by
  obtain ⟨token, present, address, timestamp, word⟩ := hash_control_preparation_token hp inverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization source aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register span.controlRegister := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = span.controlStart := by rw [word, Word.ofBitVec_roundtrip]
  unfold PreparedControl
  rw [hash_preparation_value]
  exact ⟨bits ▸ read, token, present, address, timestamp, bits⟩

theorem hash_control_preparation [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p) (rotationInverse : SerializedInverse.Scale64 p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {span : Delegation.Caller.HashSpan}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (source : HashControlPreparation data program cut span) (aligned : cut % 4 = 0) :
    PreparedBoundaryExecution data before cells cut span.controlRegister (hashPreparation span) := by
  have floor := hash_control_preparation_after_initial source
  have window := mixed_window_execution hp inverse rotationInverse accepted inputs aligned aligned (by omega) (by omega)
  obtain ⟨start, finish, earlier, current, atStart, atFinish, earlierPerm, _, earlierHistory, _,
    matching, _, boundary, _⟩ := window.execution
  exact ⟨start, earlier, atStart, earlierPerm, earlierHistory, boundary,
    hash_control_preparation_at_boundary hp inverse accepted inputs source aligned matching boundary⟩

theorem literal_computed_hash_inputs [Fact p.Prime]
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (inputs : PreparedHashWindowInputs data before ca oa cells program span lower upper) :
    ComputedPreparedHashWindowInputs data before ca oa cells program span lower upper :=
  ⟨⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
      inputs.aligned, inputs.setup, inputs.tables⟩,
    inputs.family, inputs.roundsAbsent, inputs.profile, .literal inputs.preparation,
    inputs.calls, inputs.duration, inputs.beforeTerminal⟩

theorem computed_hash_memory_inputs [Fact p.Prime]
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (inputs : ComputedPreparedHashWindowInputs data before ca oa cells program span lower upper) :
    MixedMemoryInputs data program before ca oa cells := by
  refine ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables, ?_⟩
  intro row member round
  exact False.elim (inputs.roundsAbsent row member round)

theorem computed_hash_window [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) :
    JointHashWindowResult data before cells span lower upper := by
  have rotationInverse : SerializedInverse.Scale64 p := by linear_combination clockInverse
  have memory := computed_hash_memory_inputs inputs
  have floor := hash_control_preparation_after_initial inputs.preparation
  have duration := inputs.duration
  have projection := mixed_projected_window (by omega) clockInverse rotationInverse accepted memory first last
    (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, _, startBoundary, finishBoundary,
    selected, initialized, finalBoundary, target⟩ := projection.execution
  have control := hash_control_preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    first prefixMatching startBoundary
  have entry : (Cell.register span.controlRegister).read atStart = .ok span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, inputs.family, entry, inputs.calls⟩
  have result := Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target finalBoundary.1.addresses
  exact ⟨projection.requests,
    (Delegation.Caller.Proofs.window_call_count projection.requests).trans inputs.calls,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, startBoundary, finishBoundary, selected, initialized, result⟩

theorem computed_hash_reference_at_states [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before atStart atFinish : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    {start finish : List (MemoryToken p)} {spanEvents : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ComputedPreparedHashWindowInputs data before ca oa cells program span lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst))
    (matching : (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst))
    (startBoundary : NativeBoundary start atStart cells) (finishBoundary : NativeBoundary finish atFinish cells)
    (spanPerm : spanEvents.Perm ((data.windowSteps lower upper).map transferEvent))
    (spanHistory : SailHistory cells spanEvents atStart atFinish) :
    span.Result (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory := computed_hash_memory_inputs inputs
  have floor := hash_control_preparation_after_initial inputs.preparation
  have duration := inputs.duration
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    first last (by omega) (by omega) (by omega) inputs.beforeTerminal (by simpa only [inputs.calls] using duration)
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  obtain ⟨selected, initialized, terminal, target⟩ :=
    mixed_worker_window_at_states accepted memory schedule requests matching startBoundary finishBoundary spanPerm spanHistory
  have control := hash_control_preparation_at_boundary (by omega) clockInverse accepted memory inputs.preparation
    first prefixMatching startBoundary
  have entry : (Cell.register span.controlRegister).read atStart = .ok span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection lower upper start finish) atStart span :=
    ⟨inputs.tables, inputs.family, entry, inputs.calls⟩
  exact Delegation.Caller.Proofs.hash_span_at_target hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun cell member => inputs.aligned cell (List.mem_of_mem_filter member)) target terminal.1.addresses

theorem computed_hash_chain [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {firstSpan secondSpan : Delegation.Caller.HashSpan}
    {a b c d : Nat}
    (accepted : MixedMemoryAccepted data program)
    (firstInputs : ComputedPreparedHashWindowInputs data before ca oa cells program firstSpan a b)
    (secondInputs : ComputedPreparedHashWindowInputs data before ca oa cells program secondSpan c d)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0) (gap : b ≤ c) :
    PreparedHashChainResult data before cells firstSpan secondSpan a b c d := by
  have rotationInverse : SerializedInverse.Scale64 p := by linear_combination clockInverse
  have floor := hash_control_preparation_after_initial firstInputs.preparation
  have firstDuration := firstInputs.duration
  have secondDuration := secondInputs.duration
  obtain ⟨chain, history⟩ := mixed_window_chain (by omega) clockInverse rotationInverse accepted
    (computed_hash_memory_inputs firstInputs) aa ba ca' da (by omega) (by omega) gap (by omega)
  have firstResult := computed_hash_reference_at_states hp clockInverse accepted firstInputs aa ba
    history.firstPrefixMatching history.firstMatching history.firstStartBoundary history.firstFinishBoundary
    history.firstPerm history.firstHistory
  have secondResult := computed_hash_reference_at_states hp clockInverse accepted secondInputs ca' da
    history.secondPrefixMatching history.secondMatching history.secondStartBoundary history.secondFinishBoundary
    history.secondPerm history.secondHistory
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have firstRequests := request_windows size clockInverse accepted.toRequestChecks firstInputs.publicProgram aa ba (by omega)
  have secondRequests := request_windows size clockInverse accepted.toRequestChecks secondInputs.publicProgram ca' da (by omega)
  exact ⟨firstRequests, secondRequests,
    (Delegation.Caller.Proofs.window_call_count firstRequests).trans firstInputs.calls,
    (Delegation.Caller.Proofs.window_call_count secondRequests).trans secondInputs.calls,
    chain, history, firstResult, secondResult⟩

theorem computed_hash_sequence_at_segments [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {windows : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : ∀ window ∈ windows, ComputedPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    {cut : Nat} {tokens : List (MemoryToken p)} {state : State} {segments : List (WindowSegment p)}
    (ordered : WindowsOrdered cut (windows.map HashWindow.interval))
    (actual : WindowSegmentsRealize data cells cut tokens state (windows.map HashWindow.interval) segments) :
    List.Forall₂ (HashWindowResult data cells) windows segments := by
  induction windows generalizing cut tokens state segments with
  | nil =>
    cases segments with
    | nil => exact .nil
    | cons _ _ => exact False.elim actual
  | cons window rest ih =>
    cases segments with
    | nil => exact False.elim actual
    | cons segment segments =>
      obtain ⟨_, _, first, last, restOrder⟩ := ordered
      obtain ⟨_, _, _, prefixMatching, spanPerm, spanHistory, matching, startBoundary, finishBoundary, tail⟩ := actual
      have selectedInputs := inputs window (List.mem_cons_self ..)
      have result := computed_hash_reference_at_states hp clockInverse accepted selectedInputs first last
        prefixMatching matching startBoundary finishBoundary spanPerm spanHistory
      have floor := hash_control_preparation_after_initial selectedInputs.preparation
      have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
      have requests := request_windows size clockInverse accepted.toRequestChecks selectedInputs.publicProgram
        first last (by omega)
      exact .cons ⟨requests, (Delegation.Caller.Proofs.window_call_count requests).trans selectedInputs.calls, result⟩
        (ih (fun next member => inputs next (List.mem_cons_of_mem _ member)) restOrder tail)

theorem computed_hash_sequence [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (firstInputs : ComputedPreparedHashWindowInputs data before ca oa cells program first.span first.lower first.upper)
    (restInputs : ∀ window ∈ rest, ComputedPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
  have rotationInverse : SerializedInverse.Scale64 p := by linear_combination clockInverse
  have aligned : first.lower % 4 = 0 := ordered.2.2.1
  have floor := hash_control_preparation_after_initial firstInputs.preparation
  obtain ⟨sequence, actual⟩ := mixed_window_sequence (by omega) clockInverse rotationInverse accepted
    (computed_hash_memory_inputs firstInputs) aligned (by omega) ordered
  have allInputs : ∀ window ∈ first :: rest, ComputedPreparedHashWindowInputs data before ca oa cells program
      window.span window.lower window.upper := by
    intro window member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstInputs
    · exact restInputs window member
  exact ⟨sequence, actual, computed_hash_sequence_at_segments hp clockInverse accepted allInputs ordered actual.segments⟩


/-- Public preparation supplies the lower-clock bound. Native matching and the
    modular code policy derive every selected caller, request slot and worker. -/
theorem wrapped_program_hash_preparation_schedule [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)}
    {program : List UnifiedReduced.ProgramEntry} {span : Delegation.Caller.HashSpan} {lower upper : Nat}
    (setup : data.machine.rom = Setup.table before)
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : WrappedSequentialProgram program)
    (source : HashControlPreparation data program lower span)
    (region : WrappedProgramCallerRegion data program span.family lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper)
    (beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value) :
    ProgramCallerWindow data span.family lower upper := by
  have floor := hash_control_preparation_after_initial source
  exact wrapped_program_caller_window hp clockInverse setup accepted publicProgram ordinaryProgram registry region
    first last (by omega) ordered (by omega) beforeTerminal

theorem wrapped_program_computed_hash_inputs [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {window : HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedHashInputs data before ca oa cells program)
    (scope : WrappedProgramComputedHashWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    ComputedPreparedHashWindowInputs data before ca oa cells program window.span window.lower window.upper := by
  have schedule := wrapped_program_hash_preparation_schedule hp clockInverse inputs.setup accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.registry scope.preparation scope.region first last
    (by have := scope.duration; omega) scope.beforeTerminal
  refine ⟨inputs.toProtocolContextInputs, schedule.family, inputs.roundsAbsent, scope.profile,
    scope.preparation, ?_, scope.duration, scope.beforeTerminal⟩
  rw [← schedule.workerCount, schedule.machineCount, scope.duration]
  omega

theorem wrapped_program_computed_hash_window [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {window : HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedHashInputs data before ca oa cells program)
    (scope : WrappedProgramComputedHashWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0) :
    ProgramCallerWindow data window.span.family window.lower window.upper ∧
      JointHashWindowResult data before cells window.span window.lower window.upper := by
  exact ⟨wrapped_program_hash_preparation_schedule (by omega) clockInverse inputs.setup accepted
      inputs.publicProgram inputs.ordinaryProgram inputs.registry scope.preparation scope.region first last
      (by have := scope.duration; omega) scope.beforeTerminal,
    computed_hash_window hp clockInverse accepted
      (wrapped_program_computed_hash_inputs (by omega) clockInverse accepted inputs scope first last) first last⟩

/-- Code regions derive every window's shape before the existing source-aware
    composition realizes all gaps and references in one initialized history. -/
theorem wrapped_program_computed_hash_sequence [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (clockInverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {first : HashWindow} {rest : List HashWindow}
    (accepted : MixedMemoryAccepted data program)
    (inputs : WrappedProgramComputedHashInputs data before ca oa cells program)
    (scopes : ∀ window ∈ first :: rest, WrappedProgramComputedHashWindowInputs data program window)
    (ordered : WindowsOrdered first.lower ((first :: rest).map HashWindow.interval)) :
    PreparedHashSequenceResult data before cells first rest := by
  have aligned : ∀ {windows : List HashWindow} {cut : Nat},
      WindowsOrdered cut (windows.map HashWindow.interval) →
      ∀ window ∈ windows, window.lower % 4 = 0 ∧ window.upper % 4 = 0 := by
    intro windows
    induction windows with
    | nil => intro cut _ window member; cases member
    | cons head tail ih =>
      intro cut order window member
      obtain ⟨_, _, first, last, restOrder⟩ := order
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨first, last⟩
      · exact ih restOrder window member
  have windowInputs : ∀ window ∈ first :: rest,
      ComputedPreparedHashWindowInputs data before ca oa cells program window.span window.lower window.upper := by
    intro window member
    exact wrapped_program_computed_hash_inputs (by omega) clockInverse accepted inputs (scopes window member)
      (aligned ordered window member).1 (aligned ordered window member).2
  exact computed_hash_sequence hp clockInverse accepted (windowInputs first (List.mem_cons_self ..))
    (fun window member => windowInputs window (List.mem_cons_of_mem _ member)) ordered

end Airbender.UnifiedReduced.Caller.Proofs
