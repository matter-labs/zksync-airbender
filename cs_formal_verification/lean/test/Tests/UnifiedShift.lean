module
public import Slop.UnifiedReduced.Claims
public import Slop.UnifiedReduced.Completeness.Shift
public import Slop.ShiftBinop.PortReads
public import Slop.ShiftBinop.Ports

@[expose] public section

namespace Tests.UnifiedShift
open Airbender Arithmetic Trace Reference.RiscV
set_option warningAsError true
set_option maxRecDepth 32768

private def operation (kind : Fin 7) : ShiftBinop.Operation :=
  if kind.val = 6 then .rev8 else if kind.val % 3 = 0 then .sll else if kind.val % 3 = 1 then .srl else .sra
private def immediateForm (kind : Fin 7) : Bool := decide (3 ≤ kind.val ∧ kind.val < 6)
private def unusedRight (kind : Fin 7) : Bool := immediateForm kind || kind.val = 6
private def payload (kind : Fin 7) : BitVec 12 := if immediateForm kind then 7 else 0
private def rightWord (kind : Fin 7) : BitVec 32 := if unusedRight kind then 0 else 0x13579b1f
private def rightByte (kind : Fin 7) (i : Nat) : Nat := ((rightWord kind).extractLsb' (8 * i) 8).toNat

private def inputs (kind : Fin 7) : UnifiedReduced.Completeness.Shift :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, (operation kind).tag, immediateForm kind, (payload kind).toNat, 1,
    if unusedRight kind then 0 else 2, 3, 0x34, 0x12, 0xcd, 0xab,
    rightByte kind 0, rightByte kind 1, rightByte kind 2, rightByte kind 3, 0, 0⟩
private theorem valid (kind : Fin 7) : (inputs kind).Valid := by
  fin_cases kind <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;>
    decide

end Tests.UnifiedShift
