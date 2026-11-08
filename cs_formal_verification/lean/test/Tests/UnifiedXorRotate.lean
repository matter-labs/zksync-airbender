import Slop.UnifiedReduced.Completeness.Binary
import Human.Circuits.UnifiedReduced.Control
import Slop.Arithmetic.ShiftAssembly
import Slop.Arithmetic.SignExtend
import Slop.Arithmetic.WordBytes
import Slop.Arithmetic.WordRotation
import Slop.Trace.BytePorts
import Slop.Trace.CompositionCore
import Slop.Trace.RowContext
import Slop.UnifiedReduced.Binary
import Slop.UnifiedReduced.Values
import Slop.UnifiedReduced.WordROM
import Slop.UnifiedReduced.ZeroRegister

namespace Tests.UnifiedXorRotate
open Airbender Arithmetic UnifiedReduced Trace
set_option warningAsError true
set_option maxRecDepth 32768

private def left : BitVec 32 := 0xabcd1234
private def old : BitVec 32 := 0xef015678
private def leftByte (i : Nat) : Nat := (left.extractLsb' (8 * i) 8).toNat
private def oldByte (i : Nat) : Nat := (old.extractLsb' (8 * i) 8).toNat
private def witness (kind : Fin 4) : Completeness.Binary :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 5, 0⟩, 0, true, kind.val, false, 1, 2, 2,
    leftByte 0, leftByte 1, leftByte 2, leftByte 3, oldByte 0, oldByte 1, oldByte 2, oldByte 3,
    0x5678, 0xef01⟩
private theorem valid (kind : Fin 4) : (witness kind).Valid := by
  fin_cases kind <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩ <;>
    decide

end Tests.UnifiedXorRotate
