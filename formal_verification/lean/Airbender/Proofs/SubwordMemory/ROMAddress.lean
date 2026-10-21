import Airbender.Proofs.SubwordMemory.Address
import Airbender.Proofs.SubwordMemory.Values

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option autoImplicit false

/-- The native inverse-of-four ROM key is exactly the containing word index.
    No supplied program/table equivalence or desired ROM-read premise. -/
theorem native_rom_index {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (geometry : NativeAddress w) (range : (w 20).val < 64) :
    (romWordKey w).val = (cellWord w).value / 4 := by
  have high : w 27 = w 20 := by
    have separator := (separator_values native).2
    simpa only [Nat.mod_eq_of_lt range,ZMod.natCast_zmod_val] using separator
  have castCell : (((cellWord w).value : Nat) : ZMod mersenne31Modulus) =
      w 19 - w 22 + 65536 * w 20 := by
    simp [cellWord,Word.value,limbBase]
  have aligned : (cellWord w).value % 4 = 0 := by
    simpa only [Word.toBitVec_toNat geometry.cellBound] using geometry.aligned
  have small : (cellWord w).value / 4 < 1048576 := by
    have low := geometry.cellBound.1
    dsimp [cellWord,Word.value,limbBase] at low ⊢
    omega
  have multiple : (cellWord w).value = 4 * ((cellWord w).value / 4) := by omega
  have inverse : (536870912 : ZMod mersenne31Modulus) * 4 = 1 := by decide +kernel
  have field : romWordKey w = (((cellWord w).value / 4 : Nat) : ZMod mersenne31Modulus) := by
    unfold romWordKey
    rw [high,← castCell,multiple,Nat.cast_mul,Nat.cast_ofNat,← mul_assoc,inverse,one_mul]
    congr 1
    omega
  rw [field,ZMod.val_natCast_of_lt (lt_trans small (by decide))]

/-- The original single native ROM table supplies the complete selected word.
    Binding this public ROM to architectural instruction/data bytes is separate. -/
theorem native_rom_word {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (geometry : NativeAddress w) (load : w 12 = 0) (range : (w 20).val < 64) :
    (⟨(w 41).val,(w 42).val⟩ : Word) = Word.ofBitVec (rom.word ((cellWord w).value / 4)) := by
  have values := (rom_load_values native load range).1
  have key := native_rom_index native geometry range
  have bounds := Word.ofBitVec_bound (rom.word ((cellWord w).value / 4))
  change (rom.word ((cellWord w).value / 4)).toNat % 65536 < 65536 ∧
    (rom.word ((cellWord w).value / 4)).toNat / 65536 < 65536 at bounds
  rw [values.low,values.high,key,ZMod.val_natCast_of_lt (lt_trans bounds.1 (by decide)),
    ZMod.val_natCast_of_lt (lt_trans bounds.2 (by decide))]
  rfl

end Airbender.SubwordMemory.Proofs
