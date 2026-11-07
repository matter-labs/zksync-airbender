import Airbender.Proofs.ReducedMachine.NativeWordMemoryQueries
import Airbender.Proofs.ReducedMachine.NativeWordMemoryNumerics
import Airbender.Proofs.ReducedMachine.NativeWordMemoryTableValues

namespace Airbender.ReducedMachine.NativeWordMemoryShapeProofs
open Native Verification Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native SW admits only canonical, word-aligned RAM addresses. This uses no
    source/address/result input bound and makes no original memory-read claim. -/
theorem store_address {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus)) :
    (wordMemoryAddressWord w).Bounded ∧
      4194304 ≤ (wordMemoryAddressWord w).value ∧ (wordMemoryAddressWord w).value % 4 = 0 := by
  have fields := NativeWordMemoryQueryProofs.fields holds true mask
  have query0 := NativeQueryProofs.dynamic_queries holds 0
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 100,w 101,w 102,w 103] at query0
  rw [fields.1] at query0
  have offset := NativeWordMemoryTableValues.offset query0
  have query1 := NativeQueryProofs.dynamic_queries holds 1
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 104,w 105,w 106,w 107] at query1
  rw [fields.2.1] at query1
  have separator := NativeWordMemoryTableValues.separator query1
  have access := NativeWordMemoryAccessProofs.store_access holds mask
  have high : 64 ≤ (w 62).val := by
    by_contra small
    have inside : (w 62).val < 64 := by omega
    have zero : w 66 = 0 := by simpa [inside] using separator.2.1
    have impossible := access.ram
    rw [zero] at impossible
    exact zero_ne_one impossible
  have bitsum : (w 61).val%2+(w 61).val/2%2 = 0 := by
    have fieldSum : (((w 61).val%2+(w 61).val/2%2 : Nat) : ZMod mersenne31Modulus) = 0 := by
      simpa only [Nat.cast_add,← offset.2.1,← offset.2.2] using access.offsetSum
    have limit : (w 61).val%2+(w 61).val/2%2 < mersenne31Modulus := by
      have a := Nat.mod_lt (w 61).val (by decide : 0 < 2)
      have b := Nat.mod_lt ((w 61).val/2) (by decide : 0 < 2)
      change _ < 2147483647
      omega
    have natural := congrArg ZMod.val fieldSum
    simpa only [ZMod.val_natCast_of_lt limit,ZMod.val_zero] using natural
  have aligned : (w 61).val%4 = 0 := by omega
  refine ⟨NativeWordMemoryNumericalProofs.address_bounds holds,?_,?_⟩
  · change 4194304 ≤ (w 61).val+65536*(w 62).val
    omega
  · change ((w 61).val+65536*(w 62).val)%4 = 0
    omega

/-- LW's ROM query remains active on RAM loads. Its key is the canonical low
    address plus the high address modulo 64, and enforces word alignment. -/
theorem load_address {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) :
    (wordMemoryAddressWord w).Bounded ∧ (wordMemoryAddressWord w).value%4 = 0 ∧
      w 64 = ((if (w 62).val < 64 then 0 else 1) : Nat) ∧
      #v[w 66,w 67] =
        (NativeFixed.wordROMValue (((w 61).val+65536*((w 62).val%64))/4)).map Nat.cast := by
  have fields := NativeWordMemoryQueryProofs.fields holds false mask
  have query0 := NativeQueryProofs.dynamic_queries holds 0
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 100,w 101,w 102,w 103] at query0
  rw [fields.1] at query0
  have separator := NativeWordMemoryTableValues.separator query0
  have query1 := NativeQueryProofs.dynamic_queries holds 1
  change (NativeFixed.table (p := mersenne31Modulus)).Contains #[] #v[w 104,w 105,w 106,w 107] at query1
  rw [fields.2.1] at query1
  have rom := NativeWordMemoryTableValues.rom query1
  have low := (NativeWordMemoryNumericalProofs.address_bounds holds).1
  have shadowBound := Nat.mod_lt (w 62).val (by decide : 0 < 64)
  have keyBound : (w 61).val+65536*((w 62).val%64) < mersenne31Modulus := by
    change (w 61).val < 65536 at low
    change _ < 2147483647
    omega
  have key : (w 61+65536*w 65).val = (w 61).val+65536*((w 62).val%64) := by
    rw [separator.2.2]
    have cast : w 61+65536*((w 62).val%64 : Nat) =
        (((w 61).val+65536*((w 62).val%64) : Nat) : ZMod mersenne31Modulus) := by simp
    rw [cast,ZMod.val_natCast_of_lt keyBound]
  rw [key] at rom
  refine ⟨NativeWordMemoryNumericalProofs.address_bounds holds,?_,separator.2.1,rom.2.2⟩
  change ((w 61).val+65536*(w 62).val)%4 = 0
  have aligned := rom.2.1
  omega

end Airbender.ReducedMachine.NativeWordMemoryShapeProofs
