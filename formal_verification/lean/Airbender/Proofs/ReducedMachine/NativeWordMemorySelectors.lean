import Airbender.Proofs.ReducedMachine.NativeSelectors
import Airbender.Review.Circuits.ReducedMachine.WordMemory

namespace Airbender.ReducedMachine.NativeWordMemorySelectorProofs
open Verification Native NativeSelectorProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Expected positions are proved from the actual Boolean/packed assertions. -/
def bit (store : Bool) (slot : Nat) : Nat :=
  if store then (if slot = 1 ∨ slot = 14 then 1 else 0)
  else (if slot = 0 ∨ slot = 10 then 1 else 0)

private theorem load_flags {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = ((wordMemoryMask false) : ZMod mersenne31Modulus)) (slot : Fin 18) :
    w (17 + slot.val) = (bit false slot.val : ZMod mersenne31Modulus) := by
  have b0 : (w 17).val ≤ 1 := bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := bit_bounds holds ⟨17,by decide⟩
  have natural := packed holds
  have maskValue := congrArg ZMod.val mask
  have maskBound : (wordMemoryMask false) < mersenne31Modulus := by decide
  rw [ZMod.val_natCast_of_lt maskBound] at maskValue
  rw [maskValue] at natural
  clear mask maskValue maskBound
  fin_cases slot
  all_goals
    simp [wordMemoryMask,bit] at natural ⊢
    apply ZMod.val_injective mersenne31Modulus
    simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
    omega

private theorem store_flags {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = ((wordMemoryMask true) : ZMod mersenne31Modulus)) (slot : Fin 18) :
    w (17 + slot.val) = (bit true slot.val : ZMod mersenne31Modulus) := by
  have b0 : (w 17).val ≤ 1 := bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := bit_bounds holds ⟨17,by decide⟩
  have natural := packed holds
  have maskValue := congrArg ZMod.val mask
  have maskBound : (wordMemoryMask true) < mersenne31Modulus := by decide
  rw [ZMod.val_natCast_of_lt maskBound] at maskValue
  rw [maskValue] at natural
  clear mask maskValue maskBound
  fin_cases slot
  all_goals
    simp [wordMemoryMask,bit] at natural ⊢
    apply ZMod.val_injective mersenne31Modulus
    simp only [ZMod.val_zero,ZMod.val_one_eq_one_mod,show 1 % mersenne31Modulus = 1 by decide]
    omega

/-- Both native word-only memory profiles derive every one of the eighteen packed bits. -/
theorem flags {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (store : Bool) (mask : w 12 = (wordMemoryMask store : ZMod mersenne31Modulus)) (slot : Fin 18) :
    w (17+slot.val) = (bit store slot.val : ZMod mersenne31Modulus) := by
  cases store
  · exact load_flags holds mask slot
  · exact store_flags holds mask slot

end Airbender.ReducedMachine.NativeWordMemorySelectorProofs
