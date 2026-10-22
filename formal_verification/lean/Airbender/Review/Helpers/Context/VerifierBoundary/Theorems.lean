import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.VerifierBoundary

namespace Airbender.VerifierBoundary

/-- The typed u32 boundary splits into bounded field limbs and preserves its full PC. -/
theorem encoding_soundness {p : Nat} (hp : FieldCapacity.NoWrap p Arithmetic.limbBase) (endpoint : Endpoint) :
    (endpoint.encode (p := p)).word.Bounded ∧ (endpoint.encode (p := p)).word.toBitVec = endpoint.pc :=
  Proofs.encoding_soundness hp endpoint

/-- Accepted native state matching and external logical closure force equality
    of the entire raw terminal tuple with the typed statement contribution. -/
theorem terminal_state_soundness {p : Nat} {initial terminal : PCState.State p}
    {starts ends : List (PCState.State p)} {statement : Statement}
    (accepted : (initial :: ends).Perm (terminal :: starts))
    (binding : Binding initial starts ends statement) : terminal = statement.terminal.encode :=
  Proofs.terminal_state accepted binding

/-- The external contract derives the terminal range from canonical encoding;
    it supplies no raw-terminal bound and does not truncate either imported limb. -/
theorem terminal_bound_soundness {Kind : Type} [Trace.CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p Arithmetic.limbBase) {trace : Trace.Data p Kind} (accepted : Trace.Accepted trace)
    (closure : Closure trace.initial (trace.rows.map Trace.Row.start) (trace.rows.map Trace.Row.finish)) :
    trace.terminal.word.Bounded := Proofs.trace_terminal_bound hp accepted closure

end Airbender.VerifierBoundary
