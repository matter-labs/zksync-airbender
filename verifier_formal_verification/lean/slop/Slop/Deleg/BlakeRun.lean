import Slop.Deleg.BlakeCall

/-! Seven or ten Blake2s round calls, any mode (`blake_mode_run`); in normal mode the compression (`compress`,
`compressRounds 10`), in compression mode the two-to-one hash (`hash2`, its 10-round version). -/

namespace RV
open Spec
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem blake_mode_run (s : State) (p q : Word) (hp : Buffer p 96 128) (hq : Buffer q 64 64) (hpq : Apart p 96 q 64)
    (red right comp : Bool) (h10 : s.getReg 10 = p) (h11 : s.getReg 11 = q)
    (h12 : s.getReg 12 = bCtl red right comp 0) :
    let h := readWords s.mem p 8
    let M := bMsg right comp h (readWords s.mem q 16)
    let V := bV0 comp h (readWords s.mem (p + 32#32) 16)
    ∀ k ≤ nR red, ∃ t, calls (.replicate k .blakeRound) s = some t ∧ ChangesOnly s t p 96 12 ∧
      t.getReg 12 = bCtl red right comp k ∧ (0 < k → readWords t.mem (p + 32#32) 16 = blakeVs M V k) ∧
      readWords t.mem p 8 = (if k = nR red then blakeFinal (bH0 comp h) (blakeVs M V (nR red)) else h) := by
  intro h M V k hk
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  simp only [Apart, ROM_END, RAM_END] at hp1 hp3 hq1 hq3 hpq
  have hne : p ≠ q := fun e => by subst e; omega
  have hn10 : nR red ≤ 10 := by unfold nR; split <;> omega
  have hn0 : 0 < nR red := by unfold nR; split <;> omega
  induction k with
  | zero => exact ⟨s, rfl, .refl _ _ _ _, h12, by omega, by rw [if_neg (by omega)]⟩
  | succ k ih =>
    obtain ⟨t, hrun, hch, r12, hv, hh⟩ := ih (by omega)
    have hk7 : k < nR red := by omega
    have t10 : t.getReg 10 = p := (hch.2 10 (by decide)).trans h10
    have t11 : t.getReg 11 = q := (hch.2 11 (by decide)).trans h11
    have th : readWords t.mem p 8 = h := by rw [hh, if_neg (by omega)]
    have tq : readWords t.mem q 16 = readWords s.mem q 16 := hch.readWords q 16 (by omega) (by omega)
    have te : (if k = 0 then bV0 comp (readWords t.mem p 8) (readWords t.mem (p + 32#32) 16)
        else readWords t.mem (p + 32#32) 16) = blakeVs M V k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [List.replicate, calls, Option.some.injEq] at hrun; subst hrun; rfl
      · rw [if_neg (by omega), hv hk0]
    have hcall := blakeRound_mode_call t.mem p q ⟨by simp only [ROM_END]; omega, hp2, by simp only [RAM_END]; omega⟩
      ⟨by simp only [ROM_END]; omega, hq2, by simp only [RAM_END]; omega⟩ hne red right comp k hk7
    dsimp only at hcall
    rw [te, th, tq] at hcall
    set v' := round M (SIGMA ⟨k, by omega⟩) (blakeVs M V k) with hv'
    have hvs : blakeVs M V (k + 1) = v' := by
      rw [hv', blakeVs]; congr 2; exact Fin.ext (Nat.mod_eq_of_lt (by omega))
    set h' := if k + 1 = nR red then blakeFinal (bH0 comp h) v' else h with hh'
    have p32 : (p + 32#32).toNat = p.toNat + 32 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    obtain ⟨t', h1, m', ch', r'⟩ := calls_one (k := .blakeRound) (s := t)
      (by simp only [Delegation.effect, t10, t11, r12]; exact hcall) p 96 (by simp only [RAM_END]; omega) (show (12 : Reg) ≠ 0 by decide)
      (fun aw haw => by
        rcases List.mem_append.mp haw with h1 | h1
        · have := writesAt_in p h' (by simp only [ROM_END]; omega) (by omega) (by simp only [RAM_END]; omega) aw h1
          omega
        · have := writesAt_in (p + 32#32) v' (by simp only [ROM_END]; omega) (by omega)
            (by simp only [RAM_END]; omega) aw h1
          omega)
    refine ⟨t', by rw [calls_replicate_succ, hrun, Option.bind_some, h1], hch.trans ch', r', fun _ => ?_, ?_⟩
    · rw [m', hvs, ← List.nil_append (writesAt p h'),
        show [] ++ writesAt p h' ++ writesAt (p + 32#32) v' = writesAt p h' ++ writesAt (p + 32#32) v' ++ [] by simp]
      exact readWords_storeAll t (writesAt p h') [] (p + 32#32) v' (by omega) (by simp)
    · rw [m', ← List.nil_append (writesAt p h'), hh']
      rw [readWords_storeAll t [] (writesAt (p + 32#32) v') p _ (by omega) (fun aw haw => by
        obtain ⟨j, hj, e⟩ := writesAt_addr (p + 32#32) v' (by omega) aw haw; omega)]
      by_cases h6 : k + 1 = nR red
      · rw [if_pos h6, if_pos h6, ← hvs, h6]
      · rw [if_neg h6, if_neg h6]

theorem blakeVs_range (m v : Vector Word 16) (n : Nat) :
    (List.range n).foldl (fun v r => round m (SIGMA ⟨r % 10, Nat.mod_lt _ (by decide)⟩) v) v = blakeVs m v n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem compressRounds_eq (n : Nat) (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool)
    (e : Vector Word 16) (h12 : e[12] = t ^^^ IV 4) (h14 : e[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6) :
    compressRounds n h m t last = blakeFinal h (blakeVs m (blakeV0 h e) n) := by
  have hv : blakeV0 h e = #v[h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], IV 0, IV 1, IV 2, IV 3,
      t ^^^ IV 4, IV 5, (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6, IV 7] := by
    rw [blakeV0, h12, h14]
  rw [hv, compressRounds, blakeVs_range]
  rfl

/-- The 7-round `compress` is `compressRounds 7`. -/
theorem compress_rounds (h : Vector Word 8) (m : Vector Word 16) (t : Word) (last : Bool) :
    compress h m t last = compressRounds 7 h m t last := by
  let e : Vector Word 16 := Vector.ofFn fun i =>
    if i.val = 12 then t ^^^ IV 4 else (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6
  have e12 : e[12] = t ^^^ IV 4 := by simp [e]
  have e14 : e[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 := by simp [e]
  rw [compress_eq h m t last e e12 e14, compressRounds_eq 7 h m t last e e12 e14]

theorem blake_compress_gen (red : Bool) (s : State) (p q t : Word) (last : Bool) (hp : Buffer p 96 128)
    (hq : Buffer q 64 64) (hpq : Apart p 96 q 64) (h10 : s.getReg 10 = p) (h11 : s.getReg 11 = q)
    (h12 : s.getReg 12 = bCtl red false false 0)
    (e12 : (readWords s.mem (p + 32) 16)[12] = t ^^^ IV 4)
    (e14 : (readWords s.mem (p + 32) 16)[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6) :
    ∃ s', calls (.replicate (nR red) .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compressRounds (nR red) (readWords s.mem p 8) (readWords s.mem q 16) t last := by
  obtain ⟨s', h1, h2, -, -, h5⟩ := blake_mode_run s p q hp hq hpq red false false h10 h11 h12 _ le_rfl
  refine ⟨s', h1, h2, ?_⟩
  rw [h5, if_pos rfl, compressRounds_eq _ _ _ t last _ e12 e14]
  rfl

theorem blake_compress_run : BlakeCompressRun := by
  intro s p q t last hp hq hpq h10 h11 h12 e12 e14
  rw [compress_rounds]
  exact blake_compress_gen true s p q t last hp hq hpq h10 h11 (by rw [h12]; decide +kernel) e12 e14

theorem blake_compress_run10 : BlakeCompressRun10 := by
  intro s p q t last hp hq hpq h10 h11 h12 e12 e14
  exact blake_compress_gen false s p q t last hp hq hpq h10 h11 (by rw [h12]; decide +kernel) e12 e14

theorem vget_idx {α : Type} {n : Nat} (v : Vector α n) {i j : Nat} (hi : i < n) (hj : j < n) (h : i = j) :
    v[i] = v[j] := by subst h; rfl

theorem readWords_take (mem : Word → BitVec 8) (q : Word) :
    readWords mem q 8 = Vector.ofFn fun i : Fin 8 => (readWords mem q 16)[i.val] := by
  apply Vector.ext; intro i hi; simp [readWords]

theorem blake_hash_gen (red : Bool) (s : State) (p q : Word) (right : Bool) (hp : Buffer p 96 128)
    (hq : Buffer q 64 64) (hpq : Apart p 96 q 64) (h10 : s.getReg 10 = p) (h11 : s.getReg 11 = q)
    (h12 : s.getReg 12 = bCtl red right true 0) :
    ∃ s', calls (.replicate (nR red) .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compressRounds (nR red) (Vector.ofFn configuredIV)
        (if right then readWords s.mem q 8 ++ readWords s.mem p 8 else readWords s.mem p 8 ++ readWords s.mem q 8)
        64#32 true := by
  obtain ⟨s', h1, h2, -, -, h5⟩ := blake_mode_run s p q hp hq hpq red right true h10 h11 h12 _ le_rfl
  refine ⟨s', h1, h2, ?_⟩
  rw [h5, if_pos rfl]
  have hv : bV0 true (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16) =
      blakeV0 (Vector.ofFn configuredIV) (bV0 true (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16)) := by
    simp only [bV0, blakeV0, ite_true, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero, Vector.getElem_ofFn, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have c12 : (bV0 true (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16))[12] = 64#32 ^^^ IV 4 := by
    simp only [bV0, ite_true]; exact BitVec.xor_comm _ _
  have c14 : (bV0 true (readWords s.mem p 8) (readWords s.mem (p + 32#32) 16))[14] =
      (if true then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 := by
    simp only [bV0, ite_true]; exact BitVec.xor_comm _ _
  have ml : bMsg false true (readWords s.mem p 8) (readWords s.mem q 16) = readWords s.mem p 8 ++ readWords s.mem q 8 := by
    apply Vector.ext; intro i hi
    simp only [bMsg, Bool.false_eq_true, ↓reduceIte, Vector.getElem_ofFn, Vector.getElem_append]
    by_cases h8 : i < 8
    · simp only [h8, ↓reduceIte, Nat.mod_eq_of_lt h8, Vector.getElem_append_left h8]
    · have e : (i - 8) % 16 = i - 8 := Nat.mod_eq_of_lt (by omega)
      simp only [h8, ↓reduceIte, e, Vector.getElem_append_right (show i < 8 + 8 by omega) (by omega : 8 ≤ i),
        readWords, Vector.getElem_ofFn]
  have mr : bMsg true true (readWords s.mem p 8) (readWords s.mem q 16) = readWords s.mem q 8 ++ readWords s.mem p 8 := by
    apply Vector.ext; intro i hi
    simp only [bMsg, ↓reduceIte, Vector.getElem_ofFn, Vector.getElem_append]
    by_cases h8 : i < 8
    · have e : i % 16 = i := Nat.mod_eq_of_lt (by omega)
      simp only [h8, ↓reduceIte, e, Vector.getElem_append_left h8, readWords, Vector.getElem_ofFn]
    · have e : (i - 8) % 8 = i - 8 := Nat.mod_eq_of_lt (by omega)
      simp only [h8, ↓reduceIte, e, Vector.getElem_append_right (show i < 8 + 8 by omega) (by omega : 8 ≤ i)]
  cases right
  · rw [if_neg Bool.false_ne_true, compressRounds_eq _ _ _ _ _ _ c12 c14, ← hv, ml]
    simp only [bH0, ↓reduceIte]
  · rw [if_pos rfl, compressRounds_eq _ _ _ _ _ _ c12 c14, ← hv, mr]
    simp only [bH0, ↓reduceIte]

theorem blake_hash_run : BlakeHashRun := by
  intro s p q right hp hq hpq h10 h11 h12
  obtain ⟨s', h1, h2, h3⟩ := blake_hash_gen true s p q right hp hq hpq h10 h11
    (by rw [h12]; cases right <;> decide +kernel)
  refine ⟨s', h1, h2, ?_⟩
  rw [h3]
  cases right <;> simp only [hash2, compress_rounds, ↓reduceIte, Bool.false_eq_true] <;> rfl

theorem blake_hash_run10 : BlakeHashRun10 := by
  intro s p q right hp hq hpq h10 h11 h12
  exact blake_hash_gen false s p q right hp hq hpq h10 h11 (by rw [h12]; cases right <;> decide +kernel)

end RV
