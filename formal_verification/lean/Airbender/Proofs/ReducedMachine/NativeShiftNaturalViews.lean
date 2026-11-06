import Airbender.Proofs.ReducedMachine.NativeShiftNatural

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
private theorem first {α : Type} (a b : α) : (#v[a,b])[0] = a := rfl
private theorem second {α : Type} (a b : α) : (#v[a,b])[1] = b := rfl

theorem output0 (mode : ShiftMode) (limb amount : Nat) :
    (outputs mode limb amount)[0] = if mode = .left then (limb * 2 ^ amount) % 65536 else limb / 2 ^ amount := by
  cases mode
  · exact first _ _
  · exact first _ _
  · exact first _ _

theorem output1 (mode : ShiftMode) (limb amount : Nat) :
    (outputs mode limb amount)[1] = if mode = .left then (limb * 2 ^ amount / 65536) % 65536
      else (limb * 65536 / 2 ^ amount) % 65536 := by
  cases mode
  · exact second _ _
  · exact second _ _
  · exact second _ _

end Airbender.ReducedMachine.NativeShiftNaturalProofs
