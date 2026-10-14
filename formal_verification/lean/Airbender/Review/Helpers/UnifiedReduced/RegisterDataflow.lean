import Airbender.Review.Helpers.UnifiedReduced.RegisterChains

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public register dataflow with intervening ADDIs to other nonzero GPRs.
    Such a gap may read and refresh the tracked register; its value is preserved.
    Actual operands, tokens, selectors and intermediate states are conclusions.
    Each selected cycle is worker-free; all earlier effects remain. -/
inductive PublicRegisterDataflow [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Nat → BitVec 5 → BitVec 32 → Prop where
  | prepared {cut register value}
      (preparation : PublicRegisterPreparation data program cut register value) :
      PublicRegisterDataflow data program cut register value
  | addi {cut source register value immediate}
      (prior : PublicRegisterDataflow data program (cut - 4) source value)
      (scope : RegisterImmediatePreparation data program cut source register immediate)
      (nonzero : source ≠ 0) :
      PublicRegisterDataflow data program cut register (registerImmediateValue value immediate)
  | frame {cut register value source destination immediate}
      (prior : PublicRegisterDataflow data program (cut - 4) register value)
      (scope : RegisterImmediatePreparation data program cut source destination immediate)
      (destinationNonzero : destination ≠ 0) (preserves : destination ≠ register) :
      PublicRegisterDataflow data program cut register value

end Airbender.UnifiedReduced.Caller
