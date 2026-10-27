import Slop.ISA.Equiv.Step

/-! Sail's byte memory (`readBytes`/`writeBytes` on `Nat` addresses) vs our `RV.read`/`RV.write` (on 32-bit addresses,
little-endian): equal for 1, 2 and 4 bytes, when the access does not wrap around 2^32. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

theorem word_add_toNat (a : BitVec 32) (k : Nat) (h : a.toNat + k < 2 ^ 32) :
    (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32)]; exact Nat.mod_eq_of_lt h

theorem idx (a b : BitVec 32) (k : Nat) (h : a.toNat + k < 2 ^ 32) :
    b.toNat = a.toNat + k ↔ b = a + BitVec.ofNat 32 k := by
  rw [← word_add_toNat a k h, BitVec.toNat_inj]

theorem eqrec_cast {m k : Nat} (h : m = k) (v : BitVec m) : h ▸ v = v.cast h := by subst h; rfl

theorem readBytes_succ (m : Nat → BitVec 8) (a n : Nat) :
    readBytes m a (n + 1) = ((readBytes m (a + 1) n) ++ (m a)).cast (by omega) := by
  apply BitVec.eq_of_toNat_eq; rfl

theorem writeBytes_succ (m : Nat → BitVec 8) (a n : Nat) (v : BitVec (8 * (n + 1))) :
    writeBytes m a (n + 1) v = fun c => if c = a then (v.cast (by omega : 8 * (n + 1) = 8 + 8 * n)).extractLsb' 0 8
      else writeBytes m (a + 1) n ((v.cast (by omega : 8 * (n + 1) = 8 + 8 * n)).extractLsb' 8 (8 * n)) c := by
  funext c; simp only [writeBytes, eqrec_cast]

/-- Byte `k` of `v`. -/
abbrev byte (v : BitVec 32) (k : Nat) : BitVec 8 := (v >>> (8 * k)).setWidth 8

theorem read_eq1 (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a : BitVec 32) (h : a.toNat + 1 ≤ 2 ^ 32) : RV.read sm a 1 = (readBytes σm a.toNat 1).setWidth 32 := by
  have e : ∀ k, k < 1 → σm (a.toNat + k) = sm (a + BitVec.ofNat 32 k) := by
    intro k hk; rw [← hm, word_add_toNat a k (by omega)]
  have e0 := hm a
  have z : readBytes σm (a.toNat + 1) 0 = 0#0 := rfl
  simp only [RV.read, readBytes_succ, z]
  simp only [Nat.add_assoc, Nat.reduceAdd, e0, BitVec.add_assoc]
  try simp only [BitVec.reduceAdd]
  generalize sm a = b0
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  interval_cases j <;> simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_cast, BitVec.getLsbD_zero] <;> simp

theorem writeBytes1 (m : Nat → BitVec 8) (A : Nat) (v : BitVec 32) :
    writeBytes m A 1 (v.setWidth (8 * 1)) = fun c => if c = A then byte v 0 else m c := by
  have z : ∀ x, writeBytes m (A + 1) 0 x = m := fun _ => rfl
  simp only [writeBytes_succ, Nat.add_assoc, Nat.reduceAdd, z]
  funext c
  split_ifs <;> first | rfl | (apply BitVec.eq_of_getLsbD_eq; intro j hj; interval_cases j <;> simp)

theorem rvwrite1 (m : BitVec 32 → BitVec 8) (a v : BitVec 32) :
    RV.write m a v 1 = fun b => if b = a then byte v 0 else m b := by
  funext b
  simp only [RV.write, BitVec.add_assoc, BitVec.reduceAdd, byte, Nat.reduceMul, ← BitVec.shiftRight_add,
    Nat.reduceAdd, BitVec.ushiftRight_zero, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq]

theorem write_eq1 (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a v : BitVec 32) (h : a.toNat + 1 ≤ 2 ^ 32) (b : BitVec 32) :
    writeBytes σm a.toNat 1 (v.setWidth (8 * 1)) b.toNat = RV.write sm a v 1 b := by
  rw [writeBytes1, rvwrite1]
  beta_reduce
  simp only [BitVec.toNat_inj, hm]

theorem read_eq2 (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a : BitVec 32) (h : a.toNat + 2 ≤ 2 ^ 32) : RV.read sm a 2 = (readBytes σm a.toNat 2).setWidth 32 := by
  have e : ∀ k, k < 2 → σm (a.toNat + k) = sm (a + BitVec.ofNat 32 k) := by
    intro k hk; rw [← hm, word_add_toNat a k (by omega)]
  have e1 := e 1 (by omega); have e0 := hm a
  have z : readBytes σm (a.toNat + 2) 0 = 0#0 := rfl
  simp only [RV.read, readBytes_succ, z]
  simp only [Nat.add_assoc, Nat.reduceAdd, e0, e1, BitVec.add_assoc]
  try simp only [BitVec.reduceAdd]
  generalize sm a = b0; generalize sm (a + 1#32) = b1
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  interval_cases j <;> simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_cast, BitVec.getLsbD_zero] <;> simp

theorem writeBytes2 (m : Nat → BitVec 8) (A : Nat) (v : BitVec 32) :
    writeBytes m A 2 (v.setWidth (8 * 2)) = fun c => if c = A then byte v 0 else if c = A + 1 then byte v 1 else m c := by
  have z : ∀ x, writeBytes m (A + 2) 0 x = m := fun _ => rfl
  simp only [writeBytes_succ, Nat.add_assoc, Nat.reduceAdd, z]
  funext c
  split_ifs <;> first | rfl | (apply BitVec.eq_of_getLsbD_eq; intro j hj; interval_cases j <;> simp)

theorem rvwrite2 (m : BitVec 32 → BitVec 8) (a v : BitVec 32) :
    RV.write m a v 2 = fun b => if b = a + 1 then byte v 1 else if b = a then byte v 0 else m b := by
  funext b
  simp only [RV.write, BitVec.add_assoc, BitVec.reduceAdd, byte, Nat.reduceMul, ← BitVec.shiftRight_add,
    Nat.reduceAdd, BitVec.ushiftRight_zero, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq]

theorem write_eq2 (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a v : BitVec 32) (h : a.toNat + 2 ≤ 2 ^ 32) (b : BitVec 32) :
    writeBytes σm a.toNat 2 (v.setWidth (8 * 2)) b.toNat = RV.write sm a v 2 b := by
  rw [writeBytes2, rvwrite2]
  have i1 := idx a b 1 (by omega)
  try simp only [BitVec.ofNat_eq_ofNat] at i1
  beta_reduce
  simp only [BitVec.toNat_inj, i1, hm]
  by_cases h0 : b = a <;> by_cases h1 : b = a + 1 <;> simp_all

theorem read_eq4 (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a : BitVec 32) (h : a.toNat + 4 ≤ 2 ^ 32) : RV.read sm a 4 = (readBytes σm a.toNat 4).setWidth 32 := by
  have e : ∀ k, k < 4 → σm (a.toNat + k) = sm (a + BitVec.ofNat 32 k) := by
    intro k hk; rw [← hm, word_add_toNat a k (by omega)]
  have e1 := e 1 (by omega); have e2 := e 2 (by omega); have e3 := e 3 (by omega); have e0 := hm a
  have z : readBytes σm (a.toNat + 4) 0 = 0#0 := rfl
  simp only [RV.read, readBytes_succ, z]
  simp only [Nat.add_assoc, Nat.reduceAdd, e0, e1, e2, e3, BitVec.add_assoc]
  simp only [BitVec.reduceAdd]
  generalize sm a = b0; generalize sm (a + 1#32) = b1; generalize sm (a + 2#32) = b2; generalize sm (a + 3#32) = b3
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  interval_cases j <;> simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_cast, BitVec.getLsbD_zero] <;> simp

theorem writeBytes4 (m : Nat → BitVec 8) (A : Nat) (v : BitVec 32) :
    writeBytes m A 4 (v.setWidth (8 * 4)) = fun c => if c = A then byte v 0 else if c = A + 1 then byte v 1 else if c = A + 2 then byte v 2 else if c = A + 3 then byte v 3 else m c := by
  have z : ∀ x, writeBytes m (A + 4) 0 x = m := fun _ => rfl
  simp only [writeBytes_succ, Nat.add_assoc, Nat.reduceAdd, z]
  funext c
  split_ifs <;> first | rfl | (apply BitVec.eq_of_getLsbD_eq; intro j hj; interval_cases j <;> simp)

theorem rvwrite4 (m : BitVec 32 → BitVec 8) (a v : BitVec 32) :
    RV.write m a v 4 = fun b => if b = a + 3 then byte v 3 else if b = a + 2 then byte v 2 else if b = a + 1 then byte v 1 else if b = a then byte v 0 else m b := by
  funext b
  simp only [RV.write, BitVec.add_assoc, BitVec.reduceAdd, byte, Nat.reduceMul, ← BitVec.shiftRight_add,
    Nat.reduceAdd, BitVec.ushiftRight_zero, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq]

theorem write_eq4 (σm : Nat → BitVec 8) (sm : BitVec 32 → BitVec 8) (hm : ∀ b : BitVec 32, σm b.toNat = sm b)
    (a v : BitVec 32) (h : a.toNat + 4 ≤ 2 ^ 32) (b : BitVec 32) :
    writeBytes σm a.toNat 4 (v.setWidth (8 * 4)) b.toNat = RV.write sm a v 4 b := by
  rw [writeBytes4, rvwrite4]
  have i1 := idx a b 1 (by omega); have i2 := idx a b 2 (by omega); have i3 := idx a b 3 (by omega)
  try simp only [BitVec.ofNat_eq_ofNat] at i1 i2 i3
  beta_reduce
  simp only [BitVec.toNat_inj, i1, i2, i3, hm]
  by_cases h0 : b = a <;> by_cases h1 : b = a + 1 <;> by_cases h2 : b = a + 2 <;> by_cases h3 : b = a + 3 <;> simp_all

end Slop.Equiv
