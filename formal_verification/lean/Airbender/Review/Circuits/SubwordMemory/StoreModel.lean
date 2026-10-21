import Airbender.Review.Circuits.SubwordMemory.DataModel

namespace Airbender.SubwordMemory
open Arithmetic Verification
set_option autoImplicit false

/-- Actual third native read, preserving the old destination RAM word. -/
def oldWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 37).val,(w 38).val⟩

/-- Actual SB/SH byte effects. Reads, size, offset, alignment and selectors are
    derived from public initialization, original decoding and native acceptance.
    Original Sail memory access, exceptions and retirement remain separate. -/
structure NativeStoreEffects (w : Nat → ZMod mersenne31Modulus) (entry : ProgramEntry) : Prop where
  store : entry.data.family.mask = 1 → ∀ i : Fin 4,
    (writtenWord w).toBitVec.extractLsb' (8 * i.val) 8 =
      if (w 22).val ≤ i.val ∧ i.val < (w 22).val + entry.data.family.width
      then ((dataWord w).toBitVec.setWidth (8 * entry.data.family.width)).extractLsb'
        (8 * (i.val - (w 22).val)) 8
      else (oldWord w).toBitVec.extractLsb' (8 * i.val) 8

end Airbender.SubwordMemory
