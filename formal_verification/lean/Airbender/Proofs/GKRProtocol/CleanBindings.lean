import Airbender.Proofs.GKRProtocol.CleanArithmetic

namespace Airbender.Compiler
set_option warningAsError true
variable {F : Type}

theorem CleanExpression.assertions_only [FiniteField F] (expressions : List (_root_.Expression F))
    (environment : Environment F)
    (holds : FlatOperation.ConstraintsHoldFlat environment (expressions.map FlatOperation.assert)) :
    ∀ expression ∈ expressions, expression.eval environment = 0 := by
  induction expressions with
  | nil => intro expression member; cases member
  | cons head tail proof =>
      intro expression member
      rcases List.mem_cons.mp member with same | included
      · subst expression; exact holds.1
      · exact proof holds.2 expression included

theorem CleanExpression.retained_constraints [FiniteField F]
    (operations : List (FlatOperation F)) (expressions : List (_root_.Expression F))
    (inventory : FlatOperation.constraints operations = expressions) (environment : Environment F)
    (arithmetic : FlatOperation.ConstraintsHoldFlat environment (expressions.map FlatOperation.assert))
    (primitives : ∀ lookup ∈ FlatOperation.lookups operations, lookup.Contains environment) :
    FlatOperation.ConstraintsHoldFlat environment operations := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  refine ⟨?_, primitives⟩
  rw [inventory]
  exact assertions_only expressions environment arithmetic

end Airbender.Compiler
