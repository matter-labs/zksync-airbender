import Airbender.Proofs.UnifiedReduced.PathSpanExecution

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- Complete public protocol occurrences account for every native worker once,
    including every G/Round/Keccak index and each separate bigint occurrence. -/
theorem path_span_partition_soundness
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans) :
    PathProtocolPartition (pathProtocolOccurrences bigints spans) ∧
      data.workers.rows.length = bigints.length + (spans.map fun span => span.span.callCount).sum :=
  ⟨Proofs.path_protocol_partition accepted inputs, Proofs.path_protocol_count accepted inputs⟩

/-- Whole execution also applies when a gap modifies a protected block:
    all actual ordinary writes remain, without a grouped algorithm claim. -/
theorem path_span_realizes_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) :
    Realizes (FullStep program data.program) data.machine initial cells :=
  Proofs.path_spans_execution accepted inputs profile pc commands

/-- Complete actual-path execution and all protocol algorithms share one
    derived history. Each span independently chooses public readonly syntax or
    computed-disjoint-store syntax, preserving arbitrary seed pointers for
    readonly spans. Native controls, worker partition and value frames are
    derived; retirement/configuration, initial PC and bigint F02 stay explicit. -/
theorem path_span_execution_general_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (gaps : ∀ span ∈ spans, PathSpanGapCertificate span) :
    PathSpansResult data program initial cells bigints spans :=
  Proofs.path_spans_result_with_gap_certificates accepted inputs profile pc commands gaps

/-- Actual-PC mixed execution, complete worker partition/count and every
    complete protocol algorithm on real cut states. Ordinary branch/jump/loop
    effects remain; grouped algorithms use public RAM-readonly gap syntax.
    Retirement/code/configuration, initial PC and bigint F02 remain explicit.
    The shared native history, native reads and controller masks are derived. -/
theorem path_span_execution_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (gaps : ∀ span ∈ spans, PathSpanReadOnlyGaps span) :
    PathSpansResult data program initial cells bigints spans :=
  Proofs.path_spans_result accepted inputs profile pc commands gaps

/-- Computed disjoint scratch stores are retained in the same whole execution
    and actual gap histories. Public pointer/source dataflow and finite static
    disjointness derive protected frames; protected-block stores lack this
    grouped certificate while retaining their ordinary FullStep semantics. -/
theorem path_span_execution_computed_store_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {bigints : List (PathBigintOccurrence data)} {spans : List (PathCompleteSpan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathSpansInputs data initial ca oa cells program bigints spans)
    (profile : RetirementProfile data program initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (gaps : ∀ span ∈ spans, PathSpanComputedStoreGaps span) :
    PathSpansResult data program initial cells bigints spans :=
  Proofs.path_spans_result_computed_stores accepted inputs profile pc commands gaps

end Airbender.UnifiedReduced.Caller
