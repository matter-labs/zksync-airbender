import Slop.Block.Mem

/-! A stack frame's stores as a list: the words `v` stored at `sp - c` for each `(c, v)` (`frameWrites`), read back by
a lookup in the list (`read_frameWrites`), and memory outside the frame unchanged (`frameWrites_outside`). Proven
once; a proof about a prologue then needs no per-address arithmetic. -/

namespace RV

/-- The words `v` stored at `sp - c`, for each `(c, v)` in order (the address written as `sp + (2³² - c)`, as
programs compute it). -/
def frameWrites (m : Word → BitVec 8) (sp : Word) : List (Nat × Word) → Word → BitVec 8
  | [] => m
  | (c, v) :: l => frameWrites (write m (sp + BitVec.ofNat 32 (4294967296 - c)) v 4) sp l

/-- The last word stored at offset `c`, else `d`. -/
def frameLookup (c : Nat) (d : Word) (l : List (Nat × Word)) : Word :=
  l.foldl (fun acc p => if p.1 = c then p.2 else acc) d

/-- The address `sp - c` (written `sp + (2³² - c)`) of a frame slot: `toNat_wrap` at `k = 2³² - c`. -/
theorem frame_addr (sp : Word) (c : Nat) (hc : c ≤ sp.toNat) (hc0 : 0 < c) :
    (sp + BitVec.ofNat 32 (4294967296 - c)).toNat = sp.toNat - c := by
  have := toNat_wrap sp (4294967296 - c) (by omega) (by omega)
  omega

/-- A word at an offset in the frame reads as the last one stored there. -/
theorem read_frameWrites (sp : Word) (hsp : sp.toNat % 4 = 0) :
    ∀ (l : List (Nat × Word)) (m : Word → BitVec 8) (c : Nat),
      (∀ p ∈ l, 4 ≤ p.1 ∧ p.1 ≤ sp.toNat ∧ p.1 % 4 = 0) → 4 ≤ c → c ≤ sp.toNat → c % 4 = 0 →
      read (frameWrites m sp l) (sp + BitVec.ofNat 32 (4294967296 - c)) 4 =
        frameLookup c (read m (sp + BitVec.ofNat 32 (4294967296 - c)) 4) l
  | [], _, _, _, _, _, _ => rfl
  | (c', v) :: l, m, c, hl, h1, h2, h3 => by
    have hp := hl (c', v) List.mem_cons_self
    rw [frameWrites, read_frameWrites sp hsp l _ c (fun p hp' => hl p (List.mem_cons_of_mem _ hp')) h1 h2 h3]
    simp only [frameLookup, List.foldl_cons]
    congr 1
    by_cases he : c' = c
    · subst he; rw [if_pos rfl, read_write_same4]
    · rw [if_neg he]
      have ea := frame_addr sp c' hp.2.1 (by omega)
      have eb := frame_addr sp c h2 (by omega)
      have := sp.isLt
      exact read_write_disjoint _ _ _ _ 4 4 (by omega) (by omega) (by omega)

/-- Memory outside `[sp - D, sp - d + 4)` is not touched by stores at offsets in `[d, D]` (`4 ≤ d`). -/
theorem frameWrites_outside (sp : Word) (d D : Nat) (hd : 4 ≤ d) (hD : D ≤ sp.toNat) :
    ∀ (l : List (Nat × Word)) (m : Word → BitVec 8) (a : Word), (∀ p ∈ l, d ≤ p.1 ∧ p.1 ≤ D) →
      a.toNat + D < sp.toNat ∨ sp.toNat + 4 ≤ a.toNat + d → frameWrites m sp l a = m a
  | [], _, _, _, _ => rfl
  | (c, v) :: l, m, a, hl, ha => by
    have hp := hl (c, v) List.mem_cons_self
    rw [frameWrites, frameWrites_outside sp d D hd hD l _ a (fun p hp' => hl p (List.mem_cons_of_mem _ hp')) ha]
    have e := frame_addr sp c (by omega) (by omega)
    have := sp.isLt
    exact write_outside _ _ _ _ 4 (by omega) (by omega)

/-- A word read outside `[sp - D, sp - d + 4)` is not touched by stores at offsets in `[d, D]`. -/
theorem read_frameWrites_out (sp : Word) (d D : Nat) (hd : 4 ≤ d) (hD : D ≤ sp.toNat) (l : List (Nat × Word))
    (m : Word → BitVec 8) (b : Word) (hl : ∀ p ∈ l, d ≤ p.1 ∧ p.1 ≤ D)
    (hb : b.toNat + 4 + D ≤ sp.toNat ∨ sp.toNat + 4 ≤ b.toNat + d) (hb2 : b.toNat + 4 ≤ 2 ^ 32) :
    read (frameWrites m sp l) b 4 = read m b 4 := by
  apply read_congr; intro j hj
  apply frameWrites_outside sp d D hd hD l m _ hl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

end RV
