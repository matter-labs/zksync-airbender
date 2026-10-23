import Airbender.Review.Trace.UnifiedReduced.Paths.Spans
import Airbender.Review.Trace.Delegation.SharedSpans

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- Ordinary native instruction forms that retain every RAM value. Loads may
    refresh RAM timestamps; register writes, branches and jumps retain their
    actual GPR/link effects. No store or delegation is silently treated as inert. -/
inductive PathRamReadOnlyInstruction : SailRV32.instruction → Prop where
  | write {instruction : SailRV32.instruction} {destination : BitVec 5}
      (form : PublicRegisterWrite instruction destination) : PathRamReadOnlyInstruction instruction
  | load (immediate : BitVec 12) (source destination : BitVec 5) :
      PathRamReadOnlyInstruction (.LOAD (immediate, .Regidx source, .Regidx destination, false, 4))
  | branch (immediate : BitVec 13) (right left : BitVec 5) (operation : SailRV32.bop) :
      PathRamReadOnlyInstruction (.BTYPE (immediate, .Regidx right, .Regidx left, operation))
  | jal (immediate : BitVec 21) (destination : BitVec 5) :
      PathRamReadOnlyInstruction (.JAL (immediate, .Regidx destination))
  | jalr (immediate : BitVec 12) (source destination : BitVec 5) :
      PathRamReadOnlyInstruction (.JALR (immediate, .Regidx source, .Regidx destination))

def path_span_pointer_registers : Delegation.Caller.HashSpan → List (BitVec 5)
  | .blakeG _ | .blakeRound _ => [10, 11]
  | .keccak => [11]

def PathCompleteSpan.last (span : Delegation.Caller.HashSpan) : Fin span.callCount :=
  ⟨span.callCount - 1, by have := path_span_call_count_positive span; omega⟩

/-- The first projected algorithm scope admits ordinary RAM-readonly gaps.
    All pointer frames are public destination syntax. Span-owned caller cuts
    remain real native calls; any other delegation requires a separate derived
    disjoint-footprint certificate. No actual frame equality is an input. -/
structure PathSpanReadOnlyGaps [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) : Prop where
  code : ∀ cut, span.start (PathCompleteSpan.first span.span) + 8 ≤ cut →
    cut ≤ span.start (PathCompleteSpan.last span.span) → cut % 4 = 0 →
    (¬ ∃ i : Fin span.span.callCount, cut = span.start i + 4) →
    ∃ instruction : SailRV32.instruction,
      PathInstructionPreparation data program cut instruction ∧
      PathRamReadOnlyInstruction instruction ∧
      ∀ register ∈ path_span_pointer_registers span.span, PathRegisterFrame register instruction

/-- The existing independent complete algorithm on actual first/last RAM views.
    G protects sixteen state and sixteen message words; extended BLAKE uses
    twenty-four state/extended and sixteen message words. Keccak's proof uses
    all thirty-one physical lanes, including scratch, before projecting its
    twenty-five final logical lanes. No worker-only trace mapping is invented. -/
def PathSpanAlgorithmResult (span : Delegation.Caller.HashSpan) (before after : State) : Prop :=
  match span with
  | .blakeG reduced =>
    ∃ statePointer messagePointer : BitVec 32, ∃ input message output : Vector Word 16,
      Blake2G.WorkVector.WordMapping before after statePointer messagePointer input message output ∧
      output.map Word.value = Blake2G.WorkVector.run reduced input message
  | .blakeRound flags =>
    ∃ statePointer messagePointer : BitVec 32, ∃ input output : Blake2Round.Compression.State,
      ∃ message : Vector Word 16,
      Blake2Round.Compression.WordMapping before after statePointer messagePointer input output message ∧
      output = Blake2Round.Compression.run flags input message
  | .keccak =>
    ∃ pointer : BitVec 32, ∃ input output : Vector Nat 25,
      Keccak.Permutation.WordMapping before after pointer input output ∧
      output = Specs.Keccak256.keccakPermutation input

/-- The complete algorithm refers to actual cut states in the same global
    history. Other GPR/RAM effects and every read-refresh timestamp remain in
    that history and in the general FullStep execution. -/
def PathSpanAlgorithmAt [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (cells : List Cell) (events : List MemoryAccess) (initial : State) : Prop :=
  ∃ before after : State,
    SailHistory cells (events.filter fun event => decide
      (event.1 ≤ span.start (PathCompleteSpan.first span.span))) initial before ∧
    SailHistory cells (events.filter fun event => decide
      (span.start (PathCompleteSpan.first span.span) < event.1 ∧
        event.1 ≤ span.start (PathCompleteSpan.last span.span) + 4)) before after ∧
    PathSpanAlgorithmResult span.span before after

end Airbender.UnifiedReduced.Caller
