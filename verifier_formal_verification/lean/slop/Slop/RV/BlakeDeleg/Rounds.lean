import Slop.RV.Delegate
import Human.SpecBlake
import Mathlib.Tactic.IntervalCases

/-! Airbender's Blake2s round-function delegation (CSR `0x7c7`), 7 rounds in normal mode: one call
(`blakeRound_call`), and the seven calls of a compression (`blake_rounds`) = `Spec.compress`. -/

namespace RV
open Spec
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-- The control word before round `r` (7 rounds, normal mode): bit 16, and round `r` one-hot from bit 19. -/
def blakeCtl (r : Nat) : Word := 0x10000#32 ||| (1#32 <<< (r + 19))

/-- The working vector round 0 starts from: the state, the IV, the counter and last-block words of the extended
state. -/
def blakeV0 (h : Vector Word 8) (e : Vector Word 16) : Vector Word 16 :=
  #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3, e[12], IV 5, e[14], IV 7]

/-- Call `r` of a 7-round compression of the state at `p` (extended state at `p + 32`) with the block at `p + 128`. -/
theorem blakeRound_call (mem : Word → BitVec 8) (p : Word) (hp : ROM_END ≤ p.toNat) (ha : p.toNat % 128 = 0)
    (hr : p.toNat + 192 ≤ RAM_END) (r : Nat) (h7 : r < 7) :
    let h := readWords mem p 8
    let e := readWords mem (p + 32#32) 16
    let m := readWords mem (p + 128#32) 16
    let v' := round m (SIGMA ⟨r, by omega⟩) (if r = 0 then blakeV0 h e else e)
    Delegation.blakeRound p (p + 128#32) (blakeCtl r) mem = some
      { writes := writesAt p (if r = 6 then Vector.ofFn fun i => h[i] ^^^ v'[i.val] ^^^ v'[i.val + 8] else h) ++
          writesAt (p + 32#32) v', reg := 12, val := blakeCtl (r + 1) } := by
  intro h e m v'
  have h128 : (p + 128#32).toNat = p.toNat + 128 := by
    simp only [RAM_END] at hr; rw [BitVec.toNat_add]; simp; omega
  have hne : p ≠ p + 128#32 := fun he => by
    have := congrArg BitVec.toNat he; rw [h128] at this; omega
  have c1 : ROM_END ≤ (p + 128#32).toNat := by rw [h128]; simp only [ROM_END] at hp ⊢; omega
  have c2 : (p + 128#32).toNat + 64 ≤ RAM_END := by rw [h128]; simp only [RAM_END] at hr ⊢; omega
  have c3 : (p + 128#32).toNat % 64 = 0 := by rw [h128]; omega
  interval_cases r
  all_goals
    simp only [Delegation.blakeRound, blakeCtl, hp, ha, c1, c2, c3, ne_eq, hne, not_false_eq_true, true_and]
    simp (config := { decide := true }) only [ite_true, ite_false]
  all_goals
    simp only [v', h, e, m, blakeV0, Option.some.injEq, Effect.mk.injEq, ite_true, ite_false, and_true,
      show (p + 32 : Word) = p + 32#32 from rfl]
    refine ⟨?_, by decide⟩
    congr

/-- The working vector after `k` rounds from `v`. -/
def blakeVs (m v : Vector Word 16) : Nat → Vector Word 16
  | 0 => v
  | k + 1 => round m (SIGMA ⟨k % 10, Nat.mod_lt _ (by decide)⟩) (blakeVs m v k)

/-- The state after the seven calls. -/
def blakeFinal (h : Vector Word 8) (v : Vector Word 16) : Vector Word 8 :=
  Vector.ofFn fun i => h[i] ^^^ v[i.val] ^^^ v[i.val + 8]

theorem compress_eq (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) (e : Vector Word 16)
    (h12 : e[12] = t ^^^ IV 4) (h14 : e[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6) :
    compress h m t last = blakeFinal h (blakeVs m (blakeV0 h e) 7) := by
  have hv : blakeV0 h e = #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3,
      t ^^^ IV 4, IV 5, (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6, IV 7] := by
    rw [blakeV0, h12, h14]
  rw [hv]
  rfl

/-- What `k` calls have done: the extended state holds the working vector after `k` rounds, the state is unchanged
until the last call folds the working vector in, nothing else in memory changed. -/
def BlakeAfter (s t : State) (p : Word) (k : Nat) : Prop :=
  let h := readWords s.mem p 8
  let v := blakeVs (readWords s.mem (p + 128#32) 16) (blakeV0 h (readWords s.mem (p + 32#32) 16)) k
  t.pc = s.pc + BitVec.ofNat 32 (4 * k) ∧ t.input = s.input ∧ t.getReg 12 = blakeCtl k ∧
  (∀ r : Reg, r ≠ 12 → t.getReg r = s.getReg r) ∧
  (0 < k → readWords t.mem (p + 32#32) 16 = v) ∧
  readWords t.mem p 8 = (if k = 7 then blakeFinal h v else h) ∧
  ∀ b : Word, b.toNat < p.toNat ∨ p.toNat + 96 ≤ b.toNat → t.mem b = s.mem b

/-- A word no write touches keeps its bytes. -/
theorem storeAll_mem_other (s : State) (ws : List (Word × Word)) (b : Word)
    (h : ∀ aw ∈ ws, aw.1.toNat + 4 ≤ 2 ^ 32 ∧ (b.toNat < aw.1.toNat ∨ aw.1.toNat + 4 ≤ b.toNat)) :
    (s.storeAll ws).mem b = s.mem b := by
  induction ws generalizing s with
  | nil => rfl
  | cons aw ws ih =>
    obtain ⟨a, w⟩ := aw
    show ((s.store a w 4).storeAll ws).mem b = _
    rw [ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have := h (a, w) List.mem_cons_self
    exact write_outside s.mem a w b 4 this.2 this.1

/-- Every word of `writesAt a v` is an aligned word in RAM. -/
theorem writesAt_ok {n : Nat} (a : Word) (v : Vector Word n) (h1 : ROM_END ≤ a.toNat)
    (h2 : a.toNat + 4 * n ≤ RAM_END) (h3 : a.toNat % 4 = 0) :
    ∀ aw ∈ writesAt a v, aw.1.toNat + 4 ≤ 2 ^ 32 ∧ writable aw.1 4 ∧ aligned aw.1 4 := by
  intro aw h
  obtain ⟨j, hj, e⟩ := writesAt_addr a v (by simp only [RAM_END] at h2; omega) aw h
  simp only [writable, aligned, ROM_END, RAM_END] at *
  omega

/-- Reading memory that changed only inside `[p, p + n)`, outside it. -/
theorem read_of_outside {m m' : Word → BitVec 8} {p : Word} {n : Nat}
    (hm : ∀ b : Word, b.toNat < p.toNat ∨ p.toNat + n ≤ b.toNat → m' b = m b) (b : Word) (k : Nat)
    (h : (b.toNat + k ≤ p.toNat ∨ p.toNat + n ≤ b.toNat) ∧ b.toNat + k ≤ 2 ^ 32) : read m' b k = read m b k := by
  apply read_congr
  intro j hj
  apply hm
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem blake_calls (s : State) (p : Word) (hp : ROM_END ≤ p.toNat) (ha : p.toNat % 128 = 0)
    (hr : p.toNat + 192 ≤ RAM_END) (h10 : s.getReg 10 = p) (h11 : s.getReg 11 = p + 128#32)
    (h12 : s.getReg 12 = blakeCtl 0) (hpc : s.pc.toNat % 4 = 0) (hrom : s.pc.toNat + 28 ≤ ROM_END)
    (hcode : ∀ k < 7, read s.mem (s.pc + BitVec.ofNat 32 (4 * k)) 4 = 0x7c701073#32) :
    ∀ k ≤ 7, ∃ t, run k s = some t ∧ BlakeAfter s t p k := by
  intro k hk
  induction k with
  | zero => exact ⟨s, rfl, by simp, rfl, h12, fun _ _ => rfl, by omega, by simp, fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨t, hrun, hpc', hin, r12, rr, hv, hh, hm⟩ := ih (by omega)
    have hk7 : k < 7 := by omega
    simp only [ROM_END, RAM_END] at hp hr hrom
    have t10 : t.getReg 10 = p := (rr 10 (by decide)).trans h10
    have t11 : t.getReg 11 = p + 128#32 := (rr 11 (by decide)).trans h11
    have tpcn : t.pc.toNat = s.pc.toNat + 4 * k := by
      rw [hpc']; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hfetch : read t.mem t.pc 4 = 0x7c701073#32 := by
      rw [read_congr t.mem s.mem _ 4 (fun j hj => hm _ (Or.inl (by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))), hpc']
      exact hcode k hk7
    -- what the call reads: the state (unchanged so far), the extended state, the block (unchanged)
    have th : readWords t.mem p 8 = readWords s.mem p 8 := by rw [hh, if_neg (by omega)]
    have tm : readWords t.mem (p + 128#32) 16 = readWords s.mem (p + 128#32) 16 := by
      apply Vector.ext; intro i hi
      simp only [readWords, Vector.getElem_ofFn]
      exact read_congr _ _ _ _ (fun j hj => hm _ (Or.inr (by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)))
    have te : (if k = 0 then blakeV0 (readWords t.mem p 8) (readWords t.mem (p + 32#32) 16)
        else readWords t.mem (p + 32#32) 16) =
        blakeVs (readWords s.mem (p + 128#32) 16) (blakeV0 (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16)) k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [run] at hrun; cases hrun; rfl
      · rw [if_neg (by omega), hv hk0]
    have hcall := blakeRound_call t.mem p (by simp only [ROM_END]; omega) ha (by simp only [RAM_END]; omega) k hk7
    dsimp only at hcall
    rw [te, th, tm] at hcall
    set v' := round (readWords s.mem (p + 128#32) 16) (SIGMA ⟨k, by omega⟩)
      (blakeVs (readWords s.mem (p + 128#32) 16)
        (blakeV0 (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16)) k) with hv'
    have hvs : blakeVs (readWords s.mem (p + 128#32) 16)
        (blakeV0 (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16)) (k + 1) = v' := by
      rw [hv', blakeVs]; congr 2; exact Fin.ext (Nat.mod_eq_of_lt (by omega))
    set h' := if k = 6 then blakeFinal (readWords s.mem p 8) v' else readWords s.mem p 8 with hh'
    set ws := writesAt p h' ++ writesAt (p + 32#32) v' with hws
    have p32 : (p + 32#32).toNat = p.toNat + 32 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have wok : ∀ aw ∈ ws, aw.1.toNat + 4 ≤ 2 ^ 32 ∧ writable aw.1 4 ∧ aligned aw.1 4 ∧
        p.toNat ≤ aw.1.toNat ∧ aw.1.toNat + 4 ≤ p.toNat + 96 := by
      intro aw haw
      rcases List.mem_append.mp haw with h1 | h1
      · obtain ⟨j, hj, e⟩ := writesAt_addr p h' (by omega) aw h1
        simp only [writable, aligned, ROM_END, RAM_END]; omega
      · obtain ⟨j, hj, e⟩ := writesAt_addr (p + 32#32) v' (by omega) aw h1
        simp only [writable, aligned, ROM_END, RAM_END]; omega
    have happ : ∃ t', t.applyEffect { writes := ws, reg := 12, val := blakeCtl (k + 1) } = some t' := by
      unfold State.applyEffect
      rw [if_pos (List.all_eq_true.mpr fun aw haw => decide_eq_true ⟨(wok aw haw).2.1, (wok aw haw).2.2.1⟩)]
      exact ⟨_, rfl⟩
    obtain ⟨t', ht'⟩ := happ
    obtain ⟨m', pc', in', rg'⟩ := applyEffect_some ht'
    have hstep : step t = some t' := step_delegate t t' _ .blakeRound _
      (by rw [tpcn]; omega) (by rw [tpcn]; simp only [ROM_END]; omega) hfetch rfl
      (by simp only [Delegation.effect, t10, t11, r12]; exact hcall) ht'
    refine ⟨t', by rw [run_add, hrun, Option.bind_some, run_succ, hstep]; rfl, ?_, by rw [in', hin], ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc', hpc', BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]; omega
    · rw [rg']; simp
    · intro r hr; rw [rg', if_neg (by tauto), rr r hr]
    · intro _
      rw [m', hvs, hws, ← List.nil_append (writesAt p h'), List.append_assoc,
        show writesAt p h' ++ writesAt (p + 32#32) v' = writesAt p h' ++ writesAt (p + 32#32) v' ++ [] by simp]
      exact readWords_storeAll t (writesAt p h') [] (p + 32#32) v' (by omega) (by simp)
    · rw [m', hws, ← List.nil_append (writesAt p h'), hh', hvs]
      rw [readWords_storeAll t [] (writesAt (p + 32#32) v') p _ (by omega) (fun aw haw => by
        obtain ⟨j, hj, e⟩ := writesAt_addr (p + 32#32) v' (by omega) aw haw; omega)]
      by_cases h6 : k = 6
      · subst h6; simp
      · rw [if_neg h6, if_neg (by omega)]
    · intro b hb
      rw [m', storeAll_mem_other t ws b (fun aw haw => by have := wok aw haw; omega), hm b hb]

end RV
