import Slop.Sym.Sound

/-! # Discharging side conditions by computation

The side conditions of a run are checked against a few facts the user proves once: for each base node a RAM
region (bytes `[val b + lo, val b + hi)` in RAM, `val b` aligned to `al`), and which regions are apart. Offsets are
read as signed (`BitVec.toInt`), as compiled code uses them (`sp - 16`). -/

namespace RV.Sym

variable (c : Ctx)

/-- A RAM region around the value of node `b`. -/
structure Region where
  b : Nat
  lo : Int
  hi : Int
  al : Nat
deriving DecidableEq, Repr

def Region.Holds (p : Pool) (R : Region) : Prop :=
  (ROM_END : Int) ≤ ((p.val c R.b).toNat : Int) + R.lo ∧ ((p.val c R.b).toNat : Int) + R.hi ≤ RAM_END ∧
    0 < R.al ∧ (p.val c R.b).toNat % R.al = 0

/-- Regions `R₁`, `R₂` do not overlap. -/
def Apart (p : Pool) (R₁ R₂ : Region) : Prop :=
  ((p.val c R₁.b).toNat : Int) + R₁.hi ≤ ((p.val c R₂.b).toNat : Int) + R₂.lo ∨
    ((p.val c R₂.b).toNat : Int) + R₂.hi ≤ ((p.val c R₁.b).toNat : Int) + R₁.lo

/-- `R` covers the `n` bytes at offset `k`. -/
def Region.covers (R : Region) (b : Nat) (k : Word) (n : Nat) : Bool :=
  R.b = b && decide (R.lo ≤ k.toInt) && decide (k.toInt + n ≤ R.hi)

def checkCond (rs : List Region) (aps : List (Region × Region)) : SCond → Bool
  | .aligned b k n => rs.any fun R => R.covers b k n && decide (R.al % n = 0) && decide (k.toInt % n = 0)
  | .readable b k n => rs.any fun R => R.covers b k n
  | .writable b k n => rs.any fun R => R.covers b k n
  | .disj b₁ k₁ n₁ b₂ k₂ n₂ => aps.any fun (R₁, R₂) => rs.contains R₁ && rs.contains R₂ &&
      ((R₁.covers b₁ k₁ n₁ && R₂.covers b₂ k₂ n₂) || (R₁.covers b₂ k₂ n₂ && R₂.covers b₁ k₁ n₁))

/-- The address `val b + k` of a covered access is `val b + k.toInt` (no wrap-around). -/
theorem addr_toNat (p : Pool) (R : Region) (hR : R.Holds c p) (b : Nat) (k : Word) (n : Nat)
    (hc : R.covers b k n = true) : ((p.val c b + k).toNat : Int) = (p.val c b).toNat + k.toInt := by
  simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
  obtain ⟨g1, g2, -, -⟩ := hR
  simp only [ROM_END, RAM_END] at g1 g2
  have hk := BitVec.toInt_eq_toNat_cond k
  rw [BitVec.toNat_add]
  have hv := (p.val c R.b).isLt
  split at hk <;> omega

theorem covers_bounds (p : Pool) (R : Region) (hR : R.Holds c p) (b : Nat) (k : Word) (n : Nat)
    (hc : R.covers b k n = true) :
    (ROM_END : Int) ≤ ((p.val c b + k).toNat : Int) ∧ ((p.val c b + k).toNat : Int) + n ≤ RAM_END ∧
      ((p.val c b + k).toNat : Int) = ((p.val c R.b).toNat : Int) + k.toInt := by
  have ha := addr_toNat c p R hR b k n hc
  simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
  obtain ⟨g1, g2, -, -⟩ := hR
  refine ⟨by omega, by omega, ha⟩

theorem checkCond_sound (σ : SState) (rs : List Region) (aps : List (Region × Region))
    (hR : ∀ R ∈ rs, R.Holds c σ.pool)
    (hA : ∀ q ∈ aps, q.1 ∈ rs → q.2 ∈ rs → Apart c σ.pool q.1 q.2)
    (x : SCond) (h : checkCond rs aps x = true) : x.Holds c σ := by
  cases x with
  | aligned b k n =>
    simp only [checkCond, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨R, hmem, ⟨hc, hal⟩, hk⟩ := h
    have hRh := hR R hmem
    obtain ⟨-, -, hb⟩ := covers_bounds c σ.pool R hRh b k n hc
    obtain ⟨-, -, -, hv⟩ := hRh
    simp only [SCond.Holds, RV.aligned]
    have h1 : (n : Int) ∣ ((σ.pool.val c R.b).toNat : Int) := by
      have : n ∣ (σ.pool.val c R.b).toNat :=
        Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hal) (Nat.dvd_of_mod_eq_zero hv)
      exact Int.natCast_dvd_natCast.mpr this
    have h2 : (n : Int) ∣ k.toInt := Int.dvd_of_emod_eq_zero hk
    have h3 : (n : Int) ∣ ((σ.pool.val c b + k).toNat : Int) := by rw [hb]; exact Int.dvd_add h1 h2
    exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp h3)
  | readable b k n =>
    simp only [checkCond, List.any_eq_true] at h
    obtain ⟨R, hmem, hc⟩ := h
    obtain ⟨-, h2, -⟩ := covers_bounds c σ.pool R (hR R hmem) b k n hc
    simp only [SCond.Holds, RV.readable]; simp only [RAM_END] at h2 ⊢; omega
  | writable b k n =>
    simp only [checkCond, List.any_eq_true] at h
    obtain ⟨R, hmem, hc⟩ := h
    obtain ⟨h1, h2, -⟩ := covers_bounds c σ.pool R (hR R hmem) b k n hc
    simp only [SCond.Holds, RV.writable]; simp only [ROM_END, RAM_END] at h1 h2 ⊢; omega
  | disj b₁ k₁ n₁ b₂ k₂ n₂ =>
    simp only [checkCond, List.any_eq_true] at h
    obtain ⟨⟨R₁, R₂⟩, hmem, hij⟩ := h
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hij
    obtain ⟨⟨m₁, m₂⟩, hij⟩ := hij
    · have hap := hA _ hmem m₁ m₂
      have hR₁ := hR R₁ m₁
      have hR₂ := hR R₂ m₂
      simp only [Apart] at hap
      simp only [SCond.Holds]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hij
      rcases hij with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · obtain ⟨a1, a2, a3⟩ := covers_bounds c σ.pool R₁ hR₁ b₁ k₁ n₁ c1
        obtain ⟨b1', b2', b3⟩ := covers_bounds c σ.pool R₂ hR₂ b₂ k₂ n₂ c2
        have e1 := c1; have e2 := c2
        simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at e1 e2
        simp only [ROM_END, RAM_END] at *
        omega
      · obtain ⟨a1, a2, a3⟩ := covers_bounds c σ.pool R₁ hR₁ b₂ k₂ n₂ c1
        obtain ⟨b1', b2', b3⟩ := covers_bounds c σ.pool R₂ hR₂ b₁ k₁ n₁ c2
        have e1 := c1; have e2 := c2
        simp only [Region.covers, Bool.and_eq_true, decide_eq_true_eq] at e1 e2
        simp only [ROM_END, RAM_END] at *
        omega

/-- All side conditions of a run hold, by the checker. -/
theorem conds_hold (σ : SState) (rs : List Region) (aps : List (Region × Region))
    (hR : ∀ R ∈ rs, R.Holds c σ.pool)
    (hA : ∀ q ∈ aps, q.1 ∈ rs → q.2 ∈ rs → Apart c σ.pool q.1 q.2)
    (h : σ.conds.all (checkCond rs aps) = true) : ∀ x ∈ σ.conds, x.Holds c σ := fun x hx =>
  checkCond_sound c σ rs aps hR hA x (List.all_eq_true.mp h x hx)

end RV.Sym
