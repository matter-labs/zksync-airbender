import Airbender.Proofs.ReducedMachine.NativeShiftColumns
import Airbender.Proofs.ReducedMachine.NativeShiftArithmetic

namespace Airbender.ReducedMachine.NativeShiftLowProofs
open Setup Verification NativeFixed NativeShiftArithmeticProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Compose closed certificates; run no calculation tactic in a large-getter context. -/
theorem output (i : Fin 4194304) :
    dataT37.columns[1].get? i.val = some (shiftOutputs i.val)[0] :=
  (NativeShiftColumnProofs.output ⟨0,by decide⟩ i).trans
    ((branches (i.val < 2097152)
      (NativeSllLow.data.columns[1].get? i.val)
      (NativeSrlHigh.data.columns[2].get? (i.val - 2097152))
      (some (sllHighOutput i.val)) (some (srlLowOutput (i.val - 2097152)))
      (fun left => SllLowProofs.native_low ⟨i.val,left⟩)
      (fun _ => SrlHighProofs.native_high ⟨i.val - 2097152,right_index i⟩)).trans
        (low_option i.val))

end Airbender.ReducedMachine.NativeShiftLowProofs
