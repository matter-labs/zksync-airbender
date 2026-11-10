import Airbender.Review.Helpers.UnifiedReduced.RegisterPreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- A finite public dataflow expression, rooted in a literal or AUIPC and
    extended by consecutive register-dependent ADDIs. Its value is computed from
    public instructions and placement. No actual operand or state is an input.
    Each selected preparation cycle is worker-free; earlier effects remain. -/
inductive PublicRegisterPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Nat → BitVec 5 → BitVec 32 → Prop where
  | literal {cut register literal}
      (scope : ControlPreparation data program cut register literal) :
      PublicRegisterPreparation data program cut register literal.value
  | pcRelative {cut register immediate}
      (scope : PCRelativePreparation data program cut register immediate) :
      PublicRegisterPreparation data program cut register (pcRelativeControl data cut immediate)
  | addi {cut source register value immediate}
      (prior : PublicRegisterPreparation data program (cut - 4) source value)
      (scope : RegisterImmediatePreparation data program cut source register immediate)
      (nonzero : source ≠ 0) :
      PublicRegisterPreparation data program cut register (registerImmediateValue value immediate)

end Airbender.UnifiedReduced.Caller
