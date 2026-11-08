module
public import Slop.UnifiedReduced.Completeness.Binary
public import Human.Circuits.UnifiedReduced.Control
public import Slop.Arithmetic.ShiftAssembly
public import Slop.Arithmetic.SignExtend
public import Slop.Arithmetic.WordBytes
public import Slop.Arithmetic.WordRotation
public import Slop.Trace.BytePorts
public import Slop.Trace.CompositionCore
public import Slop.Trace.RowContext
public import Slop.UnifiedReduced.Binary
public import Slop.UnifiedReduced.Values
public import Slop.UnifiedReduced.WordROM
public import Slop.UnifiedReduced.ZeroRegister

@[expose] public section

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
