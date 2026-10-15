import Airbender.Proofs.PaddingBoundary

namespace Airbender.PaddingBoundary

/-- A Boolean native selector makes the symbolic tuple contribution exactly the
    enforced mask gate, for any encoding and arbitrary native tuple values. -/
theorem contribution_soundness [Ring R] [Nontrivial R] [DecidableEq R]
    (execute : R) (boolean : execute = 0 ∨ execute = 1) (encode : α → R) (value : α) :
    evaluate encode (contribution execute value) = mask execute (encode value) :=
  Proofs.evaluate_contribution execute boolean encode value

/-- Masking an aggregate product agrees with symbolic identity factors on every
    tuple. Inactive raw PCs, clocks and memory values need not stutter. -/
theorem product_soundness [CommRing R] [Nontrivial R] [DecidableEq R]
    (execute : R) (boolean : execute = 0 ∨ execute = 1) (encode : α → R) (values : List α) :
    ((values.map (contribution execute)).map (evaluate encode)).prod =
      mask execute (values.map encode).prod :=
  Proofs.evaluate_group execute boolean encode values

/-- The full-layout external logical closure and imported constraints derive the
    old active-trace acceptance contract. All public boundaries are unchanged.
    This does not derive tuple matching from sampled scalar product equality. -/
theorem acceptance_soundness {Kind : Type} [Trace.CircuitLayout Kind] [Fact p.Prime]
    {trace : Trace.Data p Kind} (accepted : AcceptedLayout trace) : Trace.Accepted (active trace) :=
  Proofs.projected_acceptance accepted

end Airbender.PaddingBoundary
