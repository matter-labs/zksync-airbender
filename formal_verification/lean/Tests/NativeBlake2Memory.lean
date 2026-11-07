import Airbender.Review.Circuits.Blake2Worker.MemoryTheorems

namespace Airbender.Tests.NativeBlake2Memory
open Verification Blake2Worker Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem all_accesses_retained : memoryAccesses.size = 43 ∧
    (memoryAccesses.filter fun access => access.writeValue.isSome).size = 25 := MemoryProofs.access_geometry

theorem readonly_and_oldreads_retained :
    (memoryAccess ⟨0,by decide⟩).writeValue = none ∧
    (memoryAccess ⟨25,by decide⟩).writeValue = none ∧
    (memoryAccess ⟨26,by decide⟩).writeValue = none ∧
    (memoryAccess ⟨42,by decide⟩).readValue = #v[134,135] ∧
    (memoryAccess ⟨42,by decide⟩).writeValue = some #v[136,137] := by decide +kernel

theorem last_clock_coordinates :
    clockBorrowColumn ⟨42,by decide⟩ = 868 ∧
    (memoryAccess ⟨42,by decide⟩).readTime = #v[869,870] := by decide +kernel

theorem state_misalignment_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (wrong : (w 2).val % 128 ≠ 0) : False := wrong (local_memory_effects holds).stateAligned

theorem message_misalignment_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (wrong : (w 100).val % 64 ≠ 0) : False := wrong (local_memory_effects holds).messageAligned

theorem state_canonical_limit_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (large : 8388608 ≤ (w 2).val) : False := by
  have bound := (local_memory_effects holds).stateBound
  omega

theorem message_canonical_limit_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (large : 4194304 ≤ (w 100).val) : False := by
  have bound := (local_memory_effects holds).messageBound
  omega

theorem corrupt_borrow_rejected {w : Nat → ZMod mersenne31Modulus} (slot : Fin 43)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (corrupt : w (clockBorrowColumn slot) = 2) : False := by
  have bit := (local_memory_effects holds).borrowBits slot
  rw [corrupt] at bit
  have ne0 : (2 : ZMod mersenne31Modulus) ≠ 0 := by decide +kernel
  have ne1 : (2 : ZMod mersenne31Modulus) ≠ 1 := by decide +kernel
  exact bit.elim ne0 ne1

theorem low_difference_limit_rejected {w : Nat → ZMod mersenne31Modulus} (slot : Fin 43)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (large : 524288 ≤ (lowClockDifference w slot).val) : False := by
  have bound := (local_memory_effects holds).lowDifferences slot
  omega

theorem high_difference_limit_rejected {w : Nat → ZMod mersenne31Modulus} (slot : Fin 43)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (large : 524288 ≤ (highClockDifference w slot).val) : False := by
  have bound := (local_memory_effects holds).highDifferences slot
  omega

/-- Positive actual scalar slices at both largest admitted canonical pointers.
    They are not complete accepted worker rows or initialized16bit reads. -/
theorem maximal_scalar_slices :
    ((16777216 : ZMod mersenne31Modulus)*8388480).val = 65535 ∧
    ((33554432 : ZMod mersenne31Modulus)*4194240).val = 65535 := by decide +kernel

/-- Alignment/scalar acceptance alone admits a canonical value outside16bits.
    This slice makes no full-row, initialized-memory or native-defect claim. -/
theorem scalar_slice_is_not_read_range :
    ((16777216 : ZMod mersenne31Modulus)*65536).val = 512 ∧
    ((33554432 : ZMod mersenne31Modulus)*65536).val = 1024 ∧
    65536 % 128 = 0 ∧ 65536 % 64 = 0 := by decide +kernel

end Airbender.Tests.NativeBlake2Memory
