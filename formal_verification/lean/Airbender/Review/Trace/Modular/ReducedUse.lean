import Airbender.Review.Trace.Modular.ExternalCalls
import Airbender.Review.Trace.UnifiedReduced.DelegationUse

namespace Airbender.AddSub.Modular.External.Caller.ReducedUse
open Trace Reference.RiscV.Sail Reference.Sail

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public reduced-machine code partition. Every registered caller is an
extended-round micro-call; ordinary entries use the four-family registry. -/
structure Program where
  ordinary : List PooledProgramEntry
  callers : List Delegation.Caller.ProgramEntry
  bundles : List UnifiedReduced.Caller.DelegationUse.Bundle

/-- Exact public wrapper syntax and coverage. The round's control and pointer
obligations remain separate reference-state properties below. -/
structure Shapes (program : Program) : Prop where
  roundOnly : ∀ bundle ∈ program.bundles,
    ∃ reduced, bundle.kind = .round reduced
  bounds : ∀ bundle ∈ program.bundles,
    bundle.start.toNat % 4 = 0 ∧
      bundle.start.toNat + 4 * bundle.instructions ≤ ROM.limit
  calls : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
    ∃ entry ∈ program.callers,
      entry.pc = bundle.callPC index.val ∧
      entry.data.family = .blakeRound ∧
      entry.instruction =
        UnifiedReduced.Caller.DelegationUse.csrInstruction .blakeRound
  coverage : ∀ entry ∈ program.callers,
    ∃ bundle ∈ program.bundles, ∃ index : Fin bundle.kind.calls,
      entry.pc = bundle.callPC index.val ∧ entry.data.family = .blakeRound
  disjoint : ∀ one ∈ program.bundles, ∀ two ∈ program.bundles,
    ∀ i : Fin one.instructions, ∀ j : Fin two.instructions,
      one.instructionPC i.val = two.instructionPC j.val →
        one = two ∧ i.val = j.val

/-- Reachability is quantified over the actual reduced stream relation,
including external reads and complete delegated calls. -/
def Reachable (stream : List (BitVec 32)) (program : Program)
    (initial : State) (state : State × Nat) : Prop :=
  Relation.ReflTransGen (ReducedStep stream program.ordinary program.callers)
    (initial, 0) state

/-- Public supported-use contract for every possible private external stream.
It imposes the blessed round control schedule at every reachable call without
assuming an expected output or a native witness history. -/
structure ValidDelegationUse (program : Program) (initial : State) : Prop where
  shapes : Shapes program
  initialEntry : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
    0 < index.val →
      ¬ UnifiedReduced.Caller.DelegationUse.AtPC initial
        (bundle.instructionPC index.val)
  entry : ∀ stream before after,
    Reachable stream program initial before →
    ReducedStep stream program.ordinary program.callers before after →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
      0 < index.val →
      UnifiedReduced.Caller.DelegationUse.AtPC after.1
        (bundle.instructionPC index.val) →
      UnifiedReduced.Caller.DelegationUse.AtPC before.1
        (bundle.instructionPC (index.val - 1))
  arguments : ∀ stream state,
    Reachable stream program initial state →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
      UnifiedReduced.Caller.DelegationUse.AtPC state.1
        (bundle.callPC index.val) →
      UnifiedReduced.Caller.DelegationUse.ArgumentsAt bundle index.val state.1

end Airbender.AddSub.Modular.External.Caller.ReducedUse
