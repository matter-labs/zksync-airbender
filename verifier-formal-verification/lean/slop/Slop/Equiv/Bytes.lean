import Slop.Equiv.MemLayers

/-! Sail's byte vectors (`bitvec_to_vecbytes`, `from_bytes_le`) round-trip, for 1, 2 and 4 bytes. -/

open Sail SailRV32 SailRV32.Functions

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem sail_int_getElem {α : Type} {n : Nat} (v : Vector α n) (i : Int) (h : i.toNat < n) :
    v[i] = v[i.toNat] := rfl

theorem bytes1 (x : BitVec 8) : bitvec_to_vecbytes (n := 1) x = #v[x.extractLsb' 0 8] := by
  ext i hi
  simp only [bitvec_to_vecbytes, Vector.getElem_ofFn, Sail.BitVec.slice]
  interval_cases i <;> rfl

theorem roundtrip1 (x : BitVec 8) : from_bytes_le (bitvec_to_vecbytes (n := 1) x) = x := by
  rw [bytes1]
  simp only [from_bytes_le, Id.run]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  interval_cases j <;> simp [sail_int_getElem, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem bytes2 (x : BitVec 16) : bitvec_to_vecbytes (n := 2) x = #v[x.extractLsb' 0 8, x.extractLsb' 8 8] := by
  ext i hi
  simp only [bitvec_to_vecbytes, Vector.getElem_ofFn, Sail.BitVec.slice]
  interval_cases i <;> rfl

theorem roundtrip2 (x : BitVec 16) : from_bytes_le (bitvec_to_vecbytes (n := 2) x) = x := by
  rw [bytes2]
  simp only [from_bytes_le, Id.run]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  interval_cases j <;> simp [sail_int_getElem, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]

theorem bytes4 (x : BitVec 32) : bitvec_to_vecbytes (n := 4) x = #v[x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8] := by
  ext i hi
  simp only [bitvec_to_vecbytes, Vector.getElem_ofFn, Sail.BitVec.slice]
  interval_cases i <;> rfl

theorem roundtrip4 (x : BitVec 32) : from_bytes_le (bitvec_to_vecbytes (n := 4) x) = x := by
  rw [bytes4]
  simp only [from_bytes_le, Id.run]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  interval_cases j <;> simp [sail_int_getElem, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]

end Slop.Equiv
