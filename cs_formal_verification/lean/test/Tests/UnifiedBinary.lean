module
public import Slop.UnifiedReduced.Claims
public import Slop.UnifiedReduced.Completeness.Binary

@[expose] public section

namespace Tests.UnifiedBinary
open Airbender Arithmetic Trace Reference.RiscV
set_option warningAsError true
set_option maxRecDepth 32768

private def operation (kind : Fin 3) : ShiftBinop.Operation :=
  if kind.val = 0 then .xor else if kind.val = 1 then .or else .and
private def inputs (kind : Fin 3) : UnifiedReduced.Completeness.Binary :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, (operation kind).tag, false, 0, false, 1, 2, 3, 0x34, 0x12, 0xcd, 0xab,
    0x78, 0x56, 0x01, 0xef, 0, 0⟩
private theorem valid (kind : Fin 3) : (inputs kind).Valid := by
  fin_cases kind <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩ <;>
    decide

end Tests.UnifiedBinary
