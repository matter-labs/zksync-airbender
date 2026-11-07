import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Context.RVPooledBoundary
import Human.Helpers.Decoder.RVExternalInput
import Human.Helpers.UnifiedReduced.RVExecutionInputs

/-! Teardown values are bounded words, conditioned on the open item `InitsTeardowns.MemoryArgumentReadsBounded`.

    The inits/teardowns circuits range-check neither the value nor the timestamp columns of a teardown tuple. Its value
    is a value some write produced (the open item: the cross-circuit memory-argument protocol is not formalised); these
    claims derive the bound from that premise and the circuits' proven write bounds (`WritesRangeCheckedClaim` and the
    trace's history from its boot seeds): the `Init` tuples write zero, and every write of an accepted, booted trace is a
    bounded word. Proven in slop/Slop/Final/Trace/TeardownBounds.lean. -/

namespace Airbender.Trace

/-- Six pooled families booted from the standalone inits/teardowns instances `inits` (standard or CSR 0x7C0-extended
    program table): if each teardown value of `inits` is the value of an `Init` tuple or of a write of the trace's
    rows, every teardown tuple carries a bounded word. -/
def TeardownsBoundedClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} {projection : RV.Instr → Option (DecoderData PooledFamily)} (table : projection = rvPooledDecoderFields ∨ projection = NonDeterminism.Pooled.rvDecoderFields) (inputs : RVPooledBootInputs trace initial cells program inits projection) (accepted : Accepted trace) (decoded : RVPooledDecoded trace program) (reads : InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes)),
    ∀ w ∈ inits, ∀ token ∈ w.teardownTokens, token.word.Bounded

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The unified reduced machine booted from its inline inits/teardowns instances `inits`: if each teardown value of
    `inits` is the value of an `Init` tuple or of a write of the trace's rows, every teardown tuple carries a bounded
    word. -/
def TeardownsBoundedClaim : Prop :=
  ∀ {trace : UnifiedTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)} (inputs : RVBootInputs trace initial cells program inits) (accepted : Accepted trace) (reads : InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes)),
    ∀ w ∈ inits, ∀ token ∈ w.teardownTokens, token.word.Bounded

end Airbender.UnifiedReduced
