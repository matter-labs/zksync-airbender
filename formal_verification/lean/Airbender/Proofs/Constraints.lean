import Clean.Circuit.Operations

namespace Airbender.Verification

/-- Extract an assertion using Clean's own constraint-satisfaction theorem. -/
theorem assertion_of_holds {F : Type} [FiniteField F]
    {ops : List (_root_.FlatOperation F)} {env : _root_.Environment F}
    (h : _root_.FlatOperation.ConstraintsHoldFlat env ops)
    (i : Fin (_root_.FlatOperation.constraints ops).length) :
    ((_root_.FlatOperation.constraints ops).get i).eval env = 0 :=
  (_root_.FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).1 _ (List.get_mem _ _)

end Airbender.Verification
