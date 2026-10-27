import Slop.ISA.Equiv.MemLayers

/-! Sail's byte vectors (`bitvec_to_vecbytes`/`from_bytes_le`, `to_bytes_le`/`vecbytes_to_bitvec`) round-trip,
for 1, 2 and 4 bytes. -/

open Sail SailRV32 SailRV32.Functions

namespace Slop.Equiv
set_option maxHeartbeats 400000

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

/-! Writes: `to_bytes_le` splits into the same bytes, `vecbytes_to_bitvec` joins them back. -/

theorem tobytes1 (x : BitVec 8) : to_bytes_le (n := 1) x = #v[x.extractLsb' 0 8] := by
  simp only [to_bytes_le, Id.run]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  simp only [vectorUpdate, vectorInit, Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb'_eq_self]
  rfl

theorem wroundtrip1 (x : BitVec 8) : vecbytes_to_bitvec (to_bytes_le (n := 1) x) = x := by
  rw [tobytes1]
  simp only [vecbytes_to_bitvec, Vector.foldl]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  interval_cases j <;> simp

theorem tobytes2 (x : BitVec 16) : to_bytes_le (n := 2) x = #v[x.extractLsb' 0 8, x.extractLsb' 8 8] := by
  simp only [to_bytes_le, Id.run]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  simp only [vectorUpdate, vectorInit, Sail.BitVec.extractLsb, BitVec.extractLsb]
  rfl

theorem wroundtrip2 (x : BitVec 16) : vecbytes_to_bitvec (to_bytes_le (n := 2) x) = x := by
  rw [tobytes2]
  simp only [vecbytes_to_bitvec, Vector.foldl]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  interval_cases j <;> simp

theorem tobytes4 (x : BitVec 32) : to_bytes_le (n := 4) x = #v[x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8] := by
  simp only [to_bytes_le, Id.run]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  simp only [vectorUpdate, vectorInit, Sail.BitVec.extractLsb, BitVec.extractLsb]
  rfl

theorem wroundtrip4 (x : BitVec 32) : vecbytes_to_bitvec (to_bytes_le (n := 4) x) = x := by
  rw [tobytes4]
  simp only [vecbytes_to_bitvec, Vector.foldl]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  interval_cases j <;> simp

theorem setWidth_extract8 (v : BitVec 8) : BitVec.setWidth 8 (Sail.BitVec.extractLsb v 7 0) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [Sail.BitVec.extractLsb, hj]

theorem setWidth_extract16 (v : BitVec 16) : BitVec.setWidth 16 (Sail.BitVec.extractLsb v 15 0) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [Sail.BitVec.extractLsb, hj]

theorem setWidth_extract32 (v : BitVec 32) : BitVec.setWidth 32 (Sail.BitVec.extractLsb v 31 0) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [Sail.BitVec.extractLsb, hj]

theorem setWidth_extract_low8 (v : BitVec 32) : BitVec.setWidth 8 (Sail.BitVec.extractLsb v 7 0) = v.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [Sail.BitVec.extractLsb, hj]

theorem setWidth_extract_low16 (v : BitVec 32) : BitVec.setWidth 16 (Sail.BitVec.extractLsb v 15 0) = v.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [Sail.BitVec.extractLsb, hj]

theorem extract_full32 (v : BitVec 32) : Sail.BitVec.extractLsb v 31 0 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [Sail.BitVec.extractLsb, hj]

end Slop.Equiv
