import Airbender.Review.Helpers.Delegation.WorkerContext

namespace Airbender.Delegation
open Trace Reference.RiscV.Sail

/-- An independent complete call relation at the actual worker's states in the
    shared native history. The relation fixes the entire call effect and frame;
    native port observations alone do not establish this proposition. -/
def ReferenceCallExecution (reference : State → State → Prop)
    (cells : List Cell) (events : List MemoryAccess) (initial finalState : State)
    (row : Row p) : Prop :=
  ∃ earlier current newer before after,
    events = newer ++ current ++ earlier ∧
    current.Perm (row.memorySteps.map transferEvent) ∧
    SailHistory cells earlier initial before ∧ SailHistory cells current before after ∧
    SailHistory cells newer after finalState ∧ reference before after

end Airbender.Delegation
