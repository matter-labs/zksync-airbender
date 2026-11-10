module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Decoder.RVExternalInput
public import Human.Helpers.UnifiedReduced.RVExecutionInputs

@[expose] public section

/-! Teardown values are bounded words, conditioned on the open item `InitsTeardowns.MemoryArgumentReadsBounded`.

    The inits/teardowns circuits range-check neither the value nor the timestamp columns of a teardown tuple. Its value
    is a value some write produced (the open item: the cross-circuit memory-argument protocol is not formalised); these
    claims derive the bound from that premise and the circuits' proven write bounds (`WritesRangeCheckedClaim` and the
    trace's history from its boot seeds): the `Init` tuples write zero, and every write of an accepted, booted trace is a
    bounded word. Scope: `writes` are the rows of the pooled or unified trace model, which carries no delegation rows;
    a teardown whose last writer is a delegation is outside these claims (the delegation writes are range-checked too,
    `Delegation.WritesRangeCheckedClaim`). Proven in slop/Slop/Final/Trace/TeardownBounds.lean. -/

namespace Airbender.Trace

/-- Six pooled families booted from the standalone inits/teardowns instances `inits` (standard or CSR 0x7C0-extended
    program table): if each teardown value of `inits` is the value of an `Init` tuple or of a write of the trace's
    rows, every teardown tuple carries a bounded word. -/
def TeardownsBoundedClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)} {projection : RV.Instr → Option (DecoderData PooledFamily)} (_table : projection = rvPooledDecoderFields ∨ projection = NonDeterminism.Pooled.rvDecoderFields) (_inputs : RVPooledBootInputs trace initial cells program inits projection) (_accepted : Accepted trace) (_decoded : RVPooledDecoded trace program) (_reads : InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes)),
    ∀ w ∈ inits, ∀ token ∈ w.teardownTokens, token.word.Bounded

/-- The assumptions of `TeardownsBoundedClaim` can be met, with a teardown tuple. -/
def TeardownsBoundedSatisfiableClaim : Prop :=
  ∃ (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) (inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout))
    (projection : RV.Instr → Option (DecoderData PooledFamily)),
    (projection = rvPooledDecoderFields ∨ projection = NonDeterminism.Pooled.rvDecoderFields) ∧
    RVPooledBootInputs trace initial cells program inits projection ∧ Accepted trace ∧
    RVPooledDecoded trace program ∧
    InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes) ∧
    ∃ w ∈ inits, ∃ token, token ∈ w.teardownTokens

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The unified reduced machine booted from its inline inits/teardowns instances `inits`: if each teardown value of
    `inits` is the value of an `Init` tuple or of a write of the trace's rows, every teardown tuple carries a bounded
    word. -/
def TeardownsBoundedClaim : Prop :=
  ∀ {trace : UnifiedTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry} {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)} (_inputs : RVBootInputs trace initial cells program inits) (_accepted : Accepted trace) (_reads : InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes)),
    ∀ w ∈ inits, ∀ token ∈ w.teardownTokens, token.word.Bounded

end Airbender.UnifiedReduced
