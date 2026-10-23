import Airbender.Review.Trace.UnifiedReduced.Paths.ControllerDataflow
import Airbender.Review.Trace.UnifiedReduced.Paths.GPointerSeed
import Airbender.Review.Trace.UnifiedReduced.PreparedRoundWindows

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- All four complete local-reference cases. Bigint retains the separate exact
    command-binding contract; hash positions cover every existing controller. -/
inductive PathCallPosition where
  | bigint
  | hash (position : HashCallPosition)

def PathCallPosition.family : PathCallPosition → Delegation.Family
  | .bigint => .bigint
  | .hash payload => payload.span.family

/-- Public instruction/dataflow computations for separated G block bases. -/
def PathGComputedPointerPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (start : Nat) : Prop :=
  ∃ stateValue messageValue : BitVec 32, stateValue ≠ messageValue ∧
    PathControllerDataflow data program start 10 stateValue ∧
    PathControllerDataflow data program start 11 messageValue

/-- G pointers may be publicly computed or arbitrary values seeded at actual
    index0 and retained through syntactic GPR frames. Native pointer reads and
    ABI separation are derived in both cases. -/
def PathGPointerPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (start : Nat) : Prop :=
  PathGComputedPointerPreparation data program start ∨ PathGPointerSeed data program start

theorem PathGPointerPreparation.of_computed [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} {start : Nat}
    (preparation : PathGComputedPointerPreparation data program start) :
    PathGPointerPreparation data program start := Or.inl preparation

theorem PathGPointerPreparation.of_seed [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} {start : Nat}
    (preparation : PathGPointerSeed data program start) :
    PathGPointerPreparation data program start := Or.inr preparation

/-- The existing G complete-call ABI requires separated block bases. Other
    families retain their existing substantive public preparation conditions. -/
def PathCallPosition.PointerPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (start : Nat) : PathCallPosition → Prop
  | .hash ⟨.blakeG _, _⟩ => PathGPointerPreparation data program start
  | _ => True

/-- Syntactic computation of the controller before a hash caller. This accepts
    no native register read or desired worker result. -/
def PathCallPosition.Preparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (start : Nat) : PathCallPosition → Prop
  | .bigint => True
  | .hash payload => PathControllerDataflow data program start
      payload.span.controlRegister payload.word.toBitVec

/-- One public protocol occurrence. Calls at the same PC have different native
    start cuts. The complete native call and actual state frame are conclusions. -/
structure PathCallPlan [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) where
  start : Nat
  position : PathCallPosition
  code : PathCallerPreparation data (start + 4) position.family
  preparation : PathCallPosition.Preparation data program start position
  pointers : PathCallPosition.PointerPreparation data program start position

/-- Public code/protocol coverage on the accepted occurrence path. Native
    request binding derives coverage of every worker, including multiplicity.
    Raw controller transport derives extended-round masks before architectural
    history. Bigint command validity remains explicit in the eventual theorem. -/
structure PathCallsInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (plans : List (PathCallPlan data program)) : Prop extends
      ProtocolContextInputs data before ca oa cells program where
  distinctPlans : (plans.map PathCallPlan.start).Nodup
  coverage : ∀ row ∈ data.machine.rows, ∀ entry ∈ data.program,
    entry.pc = row.start.word.toBitVec →
    ∃ plan ∈ plans, plan.start = Delegation.Caller.startClock row ∧
      plan.position.family = entry.data.family

/-- Actual worker controller binding, to be derived from a public call plan and
    raw matching. It is a result predicate, never a PathCallsInputs field. -/
def HashCallPosition.NativeBinding [Fact p.Prime] (position : HashCallPosition)
    (row : Delegation.Row p) : Prop :=
  row.family = position.span.family ∧
    match position.span with
    | .blakeG _ => (readToken row.assignment Blake2G.importedConstraintsMemoryPorts[8]).word = position.word
    | .blakeRound _ => (readToken row.assignment Blake2Round.importedConstraintsMemoryPorts[42]).word = position.word
    | .keccak => (readToken row.assignment Keccak.importedConstraintsMemoryPorts[0]).word = position.word

/-- Occurrence-level native matching, including the real caller slot. This is
    derived from native participation and public code coverage, not supplied. -/
def PathCallPlan.Matches [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (plan : PathCallPlan data program)
    (worker : Delegation.Row p) : Prop :=
  plan.position.family = worker.family ∧ ∃ caller ∈ data.callers,
    plan.start = Delegation.Caller.startClock caller ∧
      Delegation.Requests.fulfillment worker = request caller.assignment ∧
      Delegation.Caller.WorkerSlot caller worker

end Airbender.UnifiedReduced.Caller
