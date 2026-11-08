module
public import Slop.UnifiedReduced.Claims
public import Slop.UnifiedReduced.Completeness.Control

@[expose] public section

namespace Tests.UnifiedComparison
open Airbender Arithmetic Trace Reference.RiscV
set_option warningAsError true
set_option maxRecDepth 16384

private def witness (immediate : Bool) : UnifiedReduced.Completeness.Control :=
  ⟨⟨0, 0, 4, 0, 0, 0, 4, 0, 0, 0⟩, 2, false, 3, 0, 0, 1, 0, 0, 0, 0,
    if immediate then 65535 else 0, if immediate then 65535 else 0, 0, 0⟩
private theorem valid (immediate : Bool) : (witness immediate).Valid := by
  cases immediate <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    decide

end Tests.UnifiedComparison
