import Airbender.Proofs.ReducedMachine.NativeShiftColumns
import Airbender.Proofs.ReducedMachine.NativeShiftArithmetic

namespace Airbender.ReducedMachine.NativeShiftHighProofs
open Setup Verification NativeFixed NativeShiftArithmeticProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Compose closed certificates; run no calculation tactic in a large-getter context. -/
theorem output (i : Fin 4194304) :
    dataT37.columns[2].get? i.val = some (shiftOutputs i.val)[1] :=
  (NativeShiftColumnProofs.output ⟨1,by decide⟩ i).trans
    ((branches (i.val < 2097152)
      (NativeSllLow.data.columns[2].get? i.val)
      (NativeSrlHigh.data.columns[1].get? (i.val - 2097152))
      (some (sllLowHighOutput i.val)) (some (srlHighLowOutput (i.val - 2097152)))
      (fun left => SllLowProofs.native_high ⟨i.val,left⟩)
      (fun _ => SrlHighProofs.native_low ⟨i.val - 2097152,right_index i⟩)).trans
        (high_option i.val))

end Airbender.ReducedMachine.NativeShiftHighProofs
