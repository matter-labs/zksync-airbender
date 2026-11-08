import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Control

namespace Tests.UnifiedJump
open Airbender Arithmetic Trace Reference.RiscV
set_option warningAsError true
set_option maxRecDepth 16384

private def witness (indirect : Bool) : UnifiedReduced.Completeness.Control :=
  ⟨⟨0, 0, 4, 0, 0, 0, if indirect then 0 else 4, 0, if indirect then 4 else 0, 0⟩,
    if indirect then 1 else 0, false, 0, if indirect then 1 else 0, 0, 1,
    if indirect then 9 else 0, 0, 0, 0, 4, 0, if indirect then 9 else 0, 0⟩
private theorem valid (indirect : Bool) : (witness indirect).Valid := by
  cases indirect <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    decide

end Tests.UnifiedJump
