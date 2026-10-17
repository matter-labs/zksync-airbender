import Airbender.Review.Trace.Execution

namespace Airbender.Trace

/-- The selected v2 arithmetic profile uses the original generated Sail clauses. -/
abbrev SailStep := StepWith decoderFields Reference.RiscV.Sail.registerClause

/-- A finite sequence of original fetched/decoded normal Sail steps, including empty traces. -/
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

end Airbender.Trace
