import Airbender.Proofs.Tables.ShiftPackedRowBinding0
import Airbender.Proofs.Tables.ShiftPackedRowBinding1
import Airbender.Proofs.Tables.ShiftPackedRowBinding2
import Airbender.Proofs.Tables.ShiftPackedRowBinding3

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false

theorem numericRow_binding (lane : Fin 4) (row : Nat) (within : row < 1024) :
    numericRow lane.val row = expectedRow lane.val row := by
  fin_cases lane
  · exact beq_iff_eq.mp (List.all_eq_true.mp rows_checked0 row (List.mem_range.mpr within))
  · exact beq_iff_eq.mp (List.all_eq_true.mp rows_checked1 row (List.mem_range.mpr within))
  · exact beq_iff_eq.mp (List.all_eq_true.mp rows_checked2 row (List.mem_range.mpr within))
  · exact beq_iff_eq.mp (List.all_eq_true.mp rows_checked3 row (List.mem_range.mpr within))

end Airbender.Verification.ShiftPackedReference
