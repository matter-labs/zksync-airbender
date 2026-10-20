import Slop.Deleg.Calls
import Mathlib.Tactic.IntervalCases

/-! The Blake2s `G` delegation (CSR `0x7c8`): one call (`blakeG_call`); 56 calls are 7 rounds (`blake_g_run`). -/

namespace RV
open Spec Delegation
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- The control word before call `k` (7 rounds). -/
def gCtl (k : Nat) : Word := BitVec.ofNat 32 (0x80 + k)

/-- Call `k`: `G` number `k % 8` of round `k / 8`. -/
def gStep (m : Vector Word 16) (k : Nat) (v : Vector Word 16) : Vector Word 16 :=
  let r : Fin 10 := ⟨k / 8 % 10, Nat.mod_lt _ (by decide)⟩
  let j : Fin 8 := ⟨k % 8, Nat.mod_lt _ (by decide)⟩
  let g := gIndices j
  G v (g 0) (g 1) (g 2) (g 3) m[SIGMA r ⟨2 * j.val, by omega⟩] m[SIGMA r ⟨2 * j.val + 1, by omega⟩]

/-- The working vector after `k` calls. -/
def gs (m v : Vector Word 16) : Nat → Vector Word 16
  | 0 => v
  | k + 1 => gStep m k (gs m v k)

theorem gCtl_next : ∀ k < 56, (gCtl k &&& 0x80#32) ||| BitVec.ofNat 32 (if k % 128 + 1 < 56 then k % 128 + 1 else 0) =
    gCtl ((k + 1) % 56) := by decide +kernel

theorem blakeG_call (mem : Word → BitVec 8) (p q : Word) (hp : Buffer p 64 64) (hq : Buffer q 64 64) (hpq : p ≠ q)
    (k : Nat) (hk : k < 56) :
    Delegation.blakeG p q (gCtl k) mem = some
      { writes := writesAt p (gStep (readWords mem q 16) k (readWords mem p 16)), reg := 12,
        val := gCtl ((k + 1) % 56) } := by
  obtain ⟨hp1, hp2, -⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hn : (gCtl k).toNat = 128 + k := by
    simp only [gCtl, BitVec.toNat_ofNat]; omega
  have h7 : (gCtl k).getLsbD 7 = true := by
    rw [BitVec.getLsbD, hn, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
  have hk' : (gCtl k).toNat % 128 = k := by rw [hn]; omega
  simp only [Delegation.blakeG, hk', h7, hp1, hp2, hq1, hq2, hq3, ne_eq, hpq, not_false_eq_true, true_and,
    show (gCtl k).toNat < 256 by omega, if_pos hk, ite_true, Option.some.injEq, Effect.mk.injEq, and_true]
  refine ⟨by simp only [gStep], ?_⟩
  have := gCtl_next k hk
  rwa [Nat.mod_eq_of_lt (show k < 128 by omega)] at this

theorem gStep_eq (m v : Vector Word 16) (r j : Nat) (hr : r < 10) (hj : j < 8) :
    gStep m (8 * r + j) v = G v (gIndices ⟨j, hj⟩ 0) (gIndices ⟨j, hj⟩ 1) (gIndices ⟨j, hj⟩ 2) (gIndices ⟨j, hj⟩ 3)
      m[SIGMA ⟨r, hr⟩ ⟨2 * j, by omega⟩] m[SIGMA ⟨r, hr⟩ ⟨2 * j + 1, by omega⟩] := by
  have e1 : (⟨(8 * r + j) / 8 % 10, Nat.mod_lt _ (by decide)⟩ : Fin 10) = ⟨r, hr⟩ := Fin.ext (by simp; omega)
  have e2 : (⟨(8 * r + j) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = ⟨j, hj⟩ := Fin.ext (by simp; omega)
  have e3 : (8 * r + j) % 8 = j := by omega
  simp only [gStep, e1, e2, e3]

theorem gs_round (m v : Vector Word 16) (r : Nat) (hr : r < 10) :
    gs m v (8 * r + 8) = round m (SIGMA ⟨r, hr⟩) (gs m v (8 * r)) := by
  simp only [gs, show 8 * r + 7 = 8 * r + 7 from rfl]
  rw [gStep_eq m _ r 7 hr (by decide), gStep_eq m _ r 6 hr (by decide), gStep_eq m _ r 5 hr (by decide),
    gStep_eq m _ r 4 hr (by decide), gStep_eq m _ r 3 hr (by decide), gStep_eq m _ r 2 hr (by decide),
    gStep_eq m _ r 1 hr (by decide), show 8 * r = 8 * r + 0 from rfl, gStep_eq m _ r 0 hr (by decide)]
  rfl

theorem gs_56 (m v : Vector Word 16) :
    gs m v 56 = (List.finRange 7).foldl (fun v r => round m (SIGMA (r.castLE (by decide))) v) v := by
  rw [show (56 : Nat) = 8 * 6 + 8 from rfl, gs_round, show 8 * 6 = 8 * 5 + 8 from rfl, gs_round,
    show 8 * 5 = 8 * 4 + 8 from rfl, gs_round, show 8 * 4 = 8 * 3 + 8 from rfl, gs_round,
    show 8 * 3 = 8 * 2 + 8 from rfl, gs_round, show 8 * 2 = 8 * 1 + 8 from rfl, gs_round,
    show 8 * 1 = 8 * 0 + 8 from rfl, gs_round]
  rfl

theorem blake_g_run : BlakeGRun := by
  intro s p q hp hq hpq h10 h11 h12
  have key : ∀ k ≤ 56, ∃ t, calls (.replicate k .blakeG) s = some t ∧ ChangesOnly s t p 64 12 ∧
      t.getReg 12 = gCtl (k % 56) ∧ readWords t.mem p 16 = gs (readWords s.mem q 16) (readWords s.mem p 16) k := by
    obtain ⟨hp1, hp2, hp3⟩ := hp
    obtain ⟨hq1, hq2, hq3⟩ := hq
    simp only [ROM_END, RAM_END] at hp1 hp3 hq1 hq3
    have hap : p.toNat + 64 ≤ q.toNat ∨ q.toNat + 64 ≤ p.toNat := by
      have : p.toNat ≠ q.toNat := fun e => hpq (BitVec.eq_of_toNat_eq e)
      omega
    intro k hk
    induction k with
    | zero => exact ⟨s, rfl, .refl _ _ _ _, h12, rfl⟩
    | succ k ih =>
      obtain ⟨t, hrun, hch, r12, hv⟩ := ih (by omega)
      have t10 : t.getReg 10 = p := (hch.2 10 (by decide)).trans h10
      have t11 : t.getReg 11 = q := (hch.2 11 (by decide)).trans h11
      have tq : readWords t.mem q 16 = readWords s.mem q 16 := hch.readWords q 16 (by omega) (by omega)
      have hcall := blakeG_call t.mem p q ⟨by simp only [ROM_END]; omega, hp2, by simp only [RAM_END]; omega⟩
        ⟨by simp only [ROM_END]; omega, hq2, by simp only [RAM_END]; omega⟩ hpq k (by omega)
      rw [tq, hv] at hcall
      rw [Nat.mod_eq_of_lt (show k < 56 by omega)] at r12
      obtain ⟨t', h1, m', ch', r'⟩ := calls_one (k := .blakeG) (s := t)
        (by simp only [Delegation.effect, t10, t11, r12]; exact hcall) p 64 (by simp only [RAM_END]; omega)
        (show (12 : Reg) ≠ 0 by decide)
        (writesAt_in (n := 16) p _ (by simp only [ROM_END]; omega) (by omega) (by simp only [RAM_END]; omega))
      refine ⟨t', by rw [calls_replicate_succ, hrun, Option.bind_some, h1], hch.trans ch',
        by rw [r'], ?_⟩
      rw [m']
      exact readWords_writesAt t p _ (by omega)
  obtain ⟨t, h1, h2, h3, h4⟩ := key 56 le_rfl
  exact ⟨t, h1, h2, h3, by rw [h4, gs_56]⟩

end RV
