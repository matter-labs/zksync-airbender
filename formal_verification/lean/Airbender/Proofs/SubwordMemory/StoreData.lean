import Airbender.Proofs.SubwordMemory.LoadData
import Airbender.Proofs.SubwordMemory.StoreBounds
import Airbender.Proofs.SubwordMemory.StoreBytes
import Airbender.Review.Circuits.SubwordMemory.StoreModel

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option autoImplicit false

/-- Literal native v2 clearing and placement give complementary bytes or a
    complete replacement halfword. No aligned-domain pruning of tables occurs. -/
theorem packed_store_sum (byte highByte : Bool) {old source offset : Nat}
    (oldBound : old < 65536) (sourceBound : source < 65536) (offsetBound : offset < 4)
    (parity : offset % 2 = if highByte then 1 else 0) :
    let raw := if byte then 0 else 1
    SubwordStoreClear.cleared (old + 65536 * offset + 262144 * raw) +
      SubwordStorePlace.placed (source + 65536 * offset + 262144 * raw) =
        if byte then (if highByte then old % 256 else 256 * (old / 256)) +
          source % 256 * (if highByte then 256 else 1) else source := by
  have rawBound : (if byte then 0 else 1) < 8 := by cases byte <;> decide
  obtain ⟨ol,op,of⟩ := packed_parts oldBound offsetBound rawBound
  obtain ⟨sl,sp,sf⟩ := packed_parts sourceBound offsetBound rawBound
  simp only [SubwordStoreClear.cleared,SubwordStorePlace.placed,ol,op,of,sl,sp,sf,parity]
  cases byte <;> cases highByte <;> simp [Nat.mul_comm]

/-- The actual native writes equal the bounded natural merge. All mappings,
    selectors and packed-key ranges come from native columns and decoding. -/
theorem native_store_merge {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (byte : Bool)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) (size : w 24 = 1)
    (raw : (w 11).val = if byte then 0 else 1)
    (sourceBound : (dataWord w).Bounded) (oldBound : (oldWord w).Bounded) :
    writtenWord w = mergedStore byte (decide ((w 22).val % 2 = 1))
      (decide (2 ≤ (w 22).val)) (dataWord w) (oldWord w) := by
  let highByte : Bool := decide ((w 22).val % 2 = 1)
  let highHalf : Bool := decide (2 ≤ (w 22).val)
  let half := if highHalf then (w 38).val else (w 37).val
  let changed := if byte then (if highByte then half % 256 else 256 * (half / 256)) +
    (w 32).val % 256 * (if highByte then 256 else 1) else (w 32).val
  have offsetBound : (w 22).val < 4 := by
    rw [(accepted_offset_values native).offset]
    exact Nat.mod_lt _ (by decide)
  have parity : (w 22).val % 2 = if highByte then 1 else 0 := by
    simp only [highByte,decide_eq_true_eq]
    split_ifs <;> omega
  have functBound : (w 11).val < 8 := by rw [raw]; cases byte <;> decide
  have selected := selected_limb_bound native oldBound
  have sameHalf : (selectedLimb w 37 38).val = half := by
    simpa only [half,highHalf,decide_eq_true_eq] using selected_word native 37 38
  have clearKey := native_data_key selected offsetBound functBound
  have placeKey := native_data_key sourceBound.1 offsetBound functBound
  have bounds := store_sum_bound selected sourceBound.1 offsetBound functBound
  have replacement := packed_store_sum byte highByte (sameHalf ▸ selected) sourceBound.1 offsetBound parity
  dsimp only [dataWord] at replacement
  rw [sameHalf,raw] at bounds
  dsimp only [dataWord] at bounds
  have changedBound : changed < 65536 := by rw [replacement] at bounds; exact bounds
  have values := store_values native store
  have merged : w 41 + w 44 = (changed : Nat) := by
    rw [values.cleared,values.placed,clearKey,placeKey,sameHalf,raw,← Nat.cast_add,replacement]
  have mergedVal : (w 41 + w 44).val = changed := by
    rw [merged,ZMod.val_natCast_of_lt (lt_trans changedBound (by decide))]
  obtain ⟨low,high⟩ := store_write_mux native store
  rcases upper_bit native with lower | higher
  · have lowerVal : ¬ 2 ≤ (w 22).val := by
      have upper := (accepted_offset_values native).upper
      rw [lower] at upper
      norm_num at upper
      omega
    simp only [storeLow,storeHigh,size,lower,sub_zero,sub_self,zero_mul,one_mul,
      add_zero,zero_add] at low high
    change (⟨(w 39).val,(w 40).val⟩ : Word) = _
    rw [low,high,mergedVal]
    simp only [mergedStore,highHalf,decide_eq_true_eq,lowerVal,if_false,dataWord,oldWord,
      changed,half,highByte]
  · have higherVal : 2 ≤ (w 22).val := by
      have upper := (accepted_offset_values native).upper
      rw [higher] at upper
      have one : (1 : ZMod mersenne31Modulus).val = 1 := by decide +kernel
      rw [one] at upper
      omega
    simp only [storeLow,storeHigh,size,higher,sub_self,zero_mul,one_mul,
      add_zero,zero_add] at low high
    change (⟨(w 39).val,(w 40).val⟩ : Word) = _
    rw [low,high,mergedVal]
    simp only [mergedStore,highHalf,decide_eq_true_eq,higherVal,if_true,dataWord,oldWord,
      changed,half,highByte]

/-- Original decoded SB/SH metadata, initialized old/source bounds and the
    literal native relations derive every changed and preserved byte. -/
theorem entry_store_effect {rom : WordROM} {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (fields : DecodedFields w entry) (sourceBound : (dataWord w).Bounded)
    (oldBound : (oldWord w).Bounded) : NativeStoreEffects w entry := by
  constructor
  intro isStore
  have store : w 12 = 1 := by simpa only [isStore,Nat.cast_one] using fields.store
  have raw : (w 11).val = if entry.data.family.byte then 0 else 1 := by
    rw [(entry_raw_values fields).2.1]
    have operationRaw (operation : Operation) (stored : operation.mask = 1) :
        operation.funct3 = if operation.byte then 0 else 1 := by
      cases operation <;> simp_all [Operation.mask,Operation.byte,Operation.funct3]
    exact operationRaw _ isStore
  have controls := entry_data_controls native fields
  have merge := native_store_merge _ native store controls.1 raw sourceBound oldBound
  let highByte : Bool := decide ((w 22).val % 2 = 1)
  let highHalf : Bool := decide (2 ≤ (w 22).val)
  have bits : (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0) = (w 22).val := by
    simp only [highByte,highHalf,decide_eq_true_eq]
    split_ifs <;> omega
  have aligned : entry.data.family.byte = false → highByte = false := by
    intro half
    have even := controls.2.2.2 half (Or.inl isStore)
    simp [highByte,even]
  have bytes := merged_store_bytes _ highByte highHalf sourceBound oldBound aligned
  dsimp only at bytes
  rw [bits] at bytes
  simpa only [merge,Operation.width] using bytes

end Airbender.SubwordMemory.Proofs
