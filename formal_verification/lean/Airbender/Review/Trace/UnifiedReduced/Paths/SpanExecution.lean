import Airbender.Review.Trace.UnifiedReduced.Paths.SpanProjection
import Airbender.Review.Trace.UnifiedReduced.Paths.SpanComputedStoreGaps
import Airbender.Review.Trace.UnifiedReduced.FullCalls

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- A public caller occurrence with an actual four-tick cut. Alignment prevents
    extra vacuous plans between native machine cycles. -/
structure PathProtocolOccurrence [Fact p.Prime] (data : RequestTrace p) where
  start : Nat
  aligned : start % 4 = 0
  family : Delegation.Family
  code : PathCallerPreparation data (start + 4) family

/-- Bigint calls retain their separate exact command-binding contract. -/
structure PathBigintOccurrence [Fact p.Prime] (data : RequestTrace p) where
  start : Nat
  aligned : start % 4 = 0
  code : PathCallerPreparation data (start + 4) .bigint

def PathBigintOccurrence.occurrence [Fact p.Prime] {data : RequestTrace p}
    (call : PathBigintOccurrence data) : PathProtocolOccurrence data :=
  ⟨call.start, call.aligned, .bigint, call.code⟩

def PathCompleteSpan.occurrence [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (i : Fin span.span.callCount) : PathProtocolOccurrence data :=
  ⟨span.start i, span.aligned i, span.span.family, span.code i⟩

/-- All complete protocols and bigint occurrences, retaining their full count
    and public order. Native workers and their partition are derived. -/
def pathProtocolOccurrences [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (bigints : List (PathBigintOccurrence data))
    (spans : List (PathCompleteSpan data program)) : List (PathProtocolOccurrence data) :=
  bigints.map PathBigintOccurrence.occurrence ++
    spans.flatMap fun span => List.ofFn span.occurrence

/-- Public actual-path coverage by complete protocols and bigint calls. This
    supplies instruction/dataflow syntax, alignment and distinct occurrence
    cuts, rather than worker membership, native controls or successful calls. -/
structure PathSpansInputs [Fact p.Prime] (data : RequestTrace p) (initial : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (bigints : List (PathBigintOccurrence data)) (spans : List (PathCompleteSpan data program)) : Prop extends
      ProtocolContextInputs data initial ca oa cells program where
  distinctOccurrences : ((pathProtocolOccurrences bigints spans).map PathProtocolOccurrence.start).Nodup
  coverage : ∀ row ∈ data.machine.rows, ∀ entry ∈ data.program,
    entry.pc = row.start.word.toBitVec →
    ∃ call ∈ pathProtocolOccurrences bigints spans,
      call.start = Delegation.Caller.startClock row ∧ call.family = entry.data.family

/-- The exact complete native pool, indexed by every public occurrence once.
    This is an output predicate; no partition is assumed in PathSpansInputs. -/
def PathProtocolPartition [Fact p.Prime] {data : RequestTrace p}
    (calls : List (PathProtocolOccurrence data)) : Prop :=
  ∃ rows : Fin calls.length → Delegation.Row p,
    Function.Injective rows ∧
    (∀ i, rows i ∈ data.workers.windowRows (calls.get i).start ((calls.get i).start + 4) ∧
      (rows i).family = (calls.get i).family ∧
      (timeOfPair (Delegation.Requests.fulfillment (rows i)).time).value = (calls.get i).start + 1) ∧
    (List.ofFn rows).Perm data.workers.rows

/-- Each complete span chooses its own public gap syntax. Arbitrary-seed
    readonly spans may coexist with computed-pointer disjoint-store spans;
    native reads, actual histories and protected frames remain derived. -/
def PathSpanGapCertificate [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) : Prop :=
  PathSpanReadOnlyGaps span ∨ Nonempty (PathSpanComputedStoreGaps span)

/-- Whole actual execution, exact full native-pool count/partition, and all
    complete algorithm projections in one derived global history. History and
    worker membership are outputs rather than public input requirements. -/
structure PathSpansResult [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    [Fact babyBearModulus.Prime]
    (data : RequestTrace babyBearModulus) (program : List UnifiedReduced.ProgramEntry)
    (initial : State) (cells : List Cell) (bigints : List (PathBigintOccurrence data))
    (spans : List (PathCompleteSpan data program)) : Prop where
  execution : Realizes (FullStep program data.program) data.machine initial cells
  partition : PathProtocolPartition (pathProtocolOccurrences bigints spans)
  count : data.workers.rows.length = bigints.length + (spans.map fun span => span.span.callCount).sum
  algorithms : ∃ events : List MemoryAccess, ∃ finalState : State,
    events.Perm (data.mixedSteps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory cells events initial finalState ∧
      ∀ span ∈ spans, PathSpanAlgorithmAt span cells events initial

end Airbender.UnifiedReduced.Caller
