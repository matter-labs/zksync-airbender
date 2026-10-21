import Airbender.Proofs.SubwordMemory.PackedKeys
import Airbender.Proofs.SubwordMemory.Values

namespace Airbender.SubwordMemory.Proofs
open Verification Arithmetic
set_option autoImplicit false

/-- Complementary SB bytes cannot carry beyond the selected limb. SH replaces
    the limb; other raw funct3 rows have zero contribution in both native tables. -/
theorem store_sum_bound {old source offset funct3 : Nat}
    (oldBound : old < 65536) (sourceBound : source < 65536)
    (offsetBound : offset < 4) (functBound : funct3 < 8) :
    SubwordStoreClear.cleared (old + 65536 * offset + 262144 * funct3) +
      SubwordStorePlace.placed (source + 65536 * offset + 262144 * funct3) < 65536 := by
  obtain ⟨oldLimb,oldOffset,oldFunct⟩ := packed_parts oldBound offsetBound functBound
  obtain ⟨sourceLimb,sourceOffset,sourceFunct⟩ := packed_parts sourceBound offsetBound functBound
  simp only [SubwordStoreClear.cleared,SubwordStorePlace.placed,oldLimb,oldOffset,oldFunct,
    sourceLimb,sourceOffset,sourceFunct]
  split_ifs <;> omega

/-- The literal native clearing/placement relations and exact packed fields
    bound their sum, retaining the old and source read dependencies. -/
theorem store_merged_bound {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) (funct : (w 11).val < 8)
    (source : (⟨(w 32).val,(w 33).val⟩ : Word).Bounded)
    (old : (⟨(w 37).val,(w 38).val⟩ : Word).Bounded) :
    (w 41 + w 44).val < 65536 := by
  have values := store_values native store
  have offset : (w 22).val < 4 := by
    rw [(accepted_offset_values native).offset]
    exact Nat.mod_lt _ (by decide)
  have selected := selected_limb_bound native old
  have clearKey := native_data_key selected offset funct
  have placeKey := native_data_key source.1 offset funct
  have bound := store_sum_bound selected source.1 offset funct
  rw [← clearKey,← placeKey] at bound
  have field : w 41 + w 44 =
      ((SubwordStoreClear.cleared (dataKey w (selectedLimb w 37 38)).val +
        SubwordStorePlace.placed (dataKey w (w 32)).val : Nat) : ZMod mersenne31Modulus) := by
    rw [values.cleared,values.placed,Nat.cast_add]
  rw [field,ZMod.val_natCast_of_lt (lt_trans bound (by decide))]
  exact bound

/-- Native full-word/subword muxes preserve the other old limb. All selectors
    come from the actual constraints; local read bounds are discharged by history. -/
theorem store_written_bounds {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) (funct : (w 11).val < 8)
    (source : (⟨(w 32).val,(w 33).val⟩ : Word).Bounded)
    (old : (⟨(w 37).val,(w 38).val⟩ : Word).Bounded) :
    (⟨(w 39).val,(w 40).val⟩ : Word).Bounded := by
  have merged := store_merged_bound native store funct source old
  obtain ⟨low,high⟩ := store_write_mux native store
  rcases size_bit native with size | size <;> rcases upper_bit native with upper | upper
  all_goals simp only [storeLow,storeHigh,size,upper,sub_zero,sub_self,zero_mul,one_mul,
    add_zero,zero_add] at low high
  · simpa only [low,high] using source
  · simpa only [low,high] using source
  · exact ⟨by simpa only [low,limbBase] using merged,by simpa only [high] using old.2⟩
  · exact ⟨by simpa only [low] using old.1,by simpa only [high,limbBase] using merged⟩

end Airbender.SubwordMemory.Proofs
