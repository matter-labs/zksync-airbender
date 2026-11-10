import Airbender.Review.Trace.UnifiedReduced.Paths.GPointerSeed
import Airbender.Review.Trace.UnifiedReduced.Paths.Calls

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

theorem path_span_call_count_positive (span : Delegation.Caller.HashSpan) : 0 < span.callCount := by
  cases span with
  | blakeG reduced => cases reduced <;> decide
  | blakeRound flags => dsimp only [Delegation.Caller.HashSpan.callCount]; split_ifs <;> decide
  | keccak => decide

def PathCompleteSpan.first (span : Delegation.Caller.HashSpan) : Fin span.callCount :=
  ⟨0, path_span_call_count_positive span⟩

/-- Every position in one complete pinned protocol has its own public actual
    occurrence. Clock order is strict while PCs may branch, jump or repeat.
    Controller computations and G pointer frames are instruction/dataflow
    syntax, never native read, worker partition or successful-result inputs. -/
structure PathCompleteSpan [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) where
  span : Delegation.Caller.HashSpan
  start : Fin span.callCount → Nat
  increasing : StrictMono start
  aligned : ∀ i, start i % 4 = 0
  code : ∀ i, PathCallerPreparation data (start i + 4) span.family
  control : ∀ i, PathControllerDataflow data program (start i) span.controlRegister
    (HashCallPosition.word ⟨span, i⟩).toBitVec
  gFrames : span.family = .blakeG → ∀ i, 0 < i.val →
    PathRegisterGapFrames data program (start (PathCompleteSpan.first span) + 4) (start i) 10 ∧
      PathRegisterGapFrames data program (start (PathCompleteSpan.first span) + 4) (start i) 11

/-- Select actual native workers by invocation occurrence, including exact
    multiplicity. The native-to-index bijection and full count are conclusions. -/
def PathCompleteSpan.nativeRows [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) : List (Delegation.Row p) :=
  data.workers.rows.filter fun worker => decide (∃ i : Fin span.span.callCount,
    (timeOfPair (Delegation.Requests.fulfillment worker).time).value = span.start i + 1)

/-- Derived actual worker occurrence map, complete protocol position binding
    and exact native-list multiplicity. No grouped hash algorithm is asserted
    here: protected RAM/pointer projection across gaps is a separate proof. -/
def PathCompleteSpan.Actual [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program) : Prop :=
  ∃ rows : Fin span.span.callCount → Delegation.Row p,
    Function.Injective rows ∧
    (∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4) ∧
      HashCallPosition.NativeBinding ⟨span.span, i⟩ (rows i)) ∧
    (List.ofFn rows).Perm span.nativeRows

end Airbender.UnifiedReduced.Caller
