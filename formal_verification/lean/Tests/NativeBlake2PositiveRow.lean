import Airbender.Review.Circuits.Blake2Worker.PositiveRowTheorems
import Mathlib.Tactic.FinCases

namespace Airbender.Tests.NativeBlake2PositiveRow
open Airbender.Verification Airbender.Blake2Worker Airbender.Blake2Worker.Native PositiveRow
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem multiplicity_one : assignment constraintsABI.multiplicity = 1 := rfl

theorem abi_high_zero : assignment constraintsABI.offsetHigh = 0 := rfl

theorem raw_clock : (assignment constraintsABI.writeTime[0],assignment constraintsABI.writeTime[1]) = (3,0) := rfl

theorem all_flags_zero (slot : Fin 13) : assignment (138+slot.val) = 0 := by
  fin_cases slot <;> decide +kernel

theorem all_old_times_zero (slot : Fin 43) (lane : Fin 2) : assignment (memoryAccess slot).readTime[lane] = 0 := by
  fin_cases slot <;> fin_cases lane <;> decide +kernel

theorem all_borrows_one (slot : Fin 43) : assignment (742+3*slot.val) = 1 := by
  fin_cases slot <;> decide +kernel

theorem pointers_zero : assignment 2 = 0 ∧ assignment 3 = 0 ∧ assignment 100 = 0 ∧ assignment 101 = 0 := by
  decide +kernel

theorem control_values_zero : assignment 134 = 0 ∧ assignment 135 = 0 ∧ assignment 136 = 0 ∧ assignment 137 = 0 := by
  decide +kernel

theorem actual_complete_body : FlatOperation.ConstraintsHoldFlat (environment assignment) (constraints Fixed.table) := native_positive_body

theorem actual_processing : LocalProcessingAccepted assignment := native_positive_processing

theorem actual_zero_table_rows (kind : Fixed.Kind) :
    (Fixed.table (p := mersenne31Modulus)).Contains #[] (#v[0,0,0,(kind.tag : F)] : Vector F 4) := PositiveRowProofs.zero_member kind

theorem active_is_not_padding : assignment constraintsABI.multiplicity ≠ 0 := by
  rw [multiplicity_one]
  exact one_ne_zero

end Airbender.Tests.NativeBlake2PositiveRow
