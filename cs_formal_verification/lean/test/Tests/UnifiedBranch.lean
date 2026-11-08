module
public import Slop.UnifiedReduced.Claims
public import Slop.UnifiedReduced.Completeness.Control

@[expose] public section

namespace Tests.UnifiedBranch
open Airbender Arithmetic Trace Reference.RiscV
set_option warningAsError true
set_option maxRecDepth 16384

private def witness (taken : Bool) : UnifiedReduced.Completeness.Control :=
  ⟨⟨0, 0, 4, 0, 0, 0, 4, 0, 5, 0⟩, 3, true, if taken then 0 else 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0⟩
private theorem valid (taken : Bool) : (witness taken).Valid := by
  cases taken <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    decide

end Tests.UnifiedBranch
