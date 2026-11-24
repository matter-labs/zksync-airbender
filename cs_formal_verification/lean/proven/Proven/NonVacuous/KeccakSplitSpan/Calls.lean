module
public import Proven.NonVacuous.KeccakSplitSpan.Parity.Ports
public import Proven.NonVacuous.KeccakSplitSpan.Parity.Row
public import Proven.NonVacuous.KeccakSplitSpan.ThetaRho.Ports
public import Proven.NonVacuous.KeccakSplitSpan.ThetaRho.Row
public import Proven.NonVacuous.KeccakSplitSpan.Chi.Ports

@[expose] public section

/-! Call `k`'s honest row under the span invariant, by its worker: its read clocks are the write clocks of the calls
    that last touched its keys (`touch`), so a parity row's previous clocks are below its write clock and a
    theta+rho or chi row's grouped clocks are at their schedule distances; hence the row satisfies its constraints
    (`holds`) and does what the span's step needs (`facts`). -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Arithmetic Trace Keccak.Split Keccak.Split.SetupProofs

local notation "P" => babyBearModulus

theorem lastTouch_lt : ∀ {k key j : Nat}, lastTouch k key = some j → j < k
  | 0, _, _, touched => by simp [lastTouch] at touched
  | k + 1, key, j, touched => by
    unfold lastTouch at touched
    split_ifs at touched
    · cases touched
      omega
    · exact Nat.lt_succ_of_lt (lastTouch_lt touched)

theorem clock_lt (k key : Nat) : clockOf (lastTouch k key) < 3 + 4 * k := by
  cases touched : lastTouch k key with
  | none => simp [clockOf]
  | some j =>
    have := lastTouch_lt touched
    simp only [clockOf]
    omega

variable {mem : Memory} {k : Nat}

/-- The previous low clock at a key: the write clock of the call that last touched it. -/
theorem previous_eq (inv : Inv mem k) (call : k < 361) {key : Nat} (small : key < 62) :
    (mem key).time.1.val = clockOf (lastTouch k key) := by
  rw [inv.clock key small]
  have := clock_lt k key
  exact ZMod.val_natCast_of_lt (by unfold babyBearModulus; omega)

/-- A theta+rho or chi port's previous clock, `distance` calls back. -/
theorem grouped (inv : Inv mem k) (call : k < 361) (late : 5 ≤ k % 15) {j : Nat} (port : j < portCount k) :
    (mem (portKey k j)).time.1.val = 3 + 4 * (k - distance (k % 15) j) := by
  rw [previous_eq inv call (portKey_lt port), touch call late port]
  rfl

theorem parity_kind (kind : k % 15 < 5) : kindAt k = .columnParity := by
  rw [kindAt_eq]
  simp only [kind, ↓reduceIte]

theorem theta_kind (low : 5 ≤ k % 15) (high : k % 15 < 10) : kindAt k = .thetaRho := by
  rw [kindAt_eq]
  simp only [show ¬ k % 15 < 5 by omega, high, ↓reduceIte]

theorem chi_kind (late : 10 ≤ k % 15) : kindAt k = .chi5 := by
  rw [kindAt_eq]
  simp only [show ¬ k % 15 < 5 by omega, show ¬ k % 15 < 10 by omega, ↓reduceIte]

theorem theta_flags (x : RowInput) :
    ThetaRho.flag x 0 + 6 * ThetaRho.flag x 1 + 2 * ThetaRho.flag x 2 + 2 * ThetaRho.flag x 3 +
        2 * ThetaRho.flag x 4 = [1, 6, 2, 2, 2].getD (x.call % 5) 0 ∧
      4 * ThetaRho.flag x 0 + 4 * ThetaRho.flag x 1 + 4 * ThetaRho.flag x 2 + 3 * ThetaRho.flag x 3 +
        3 * ThetaRho.flag x 4 = [4, 4, 4, 3, 3].getD (x.call % 5) 0 := by
  rcases ThetaRho.column_cases x with c | c | c | c | c <;> simp [ThetaRho.flag, c]

theorem theta_clocks (inv : Inv mem k) (call : k < 361) (low : 5 ≤ k % 15) (high : k % 15 < 10) :
    ThetaRho.Clocks (mem.input k) := by
  have count : portCount k = 16 := by rw [portCount, theta_kind low high]; rfl
  have g (j : Nat) (h : j < 16) := grouped inv call low (j := j) (by rw [count]; exact h)
  have column : k % 15 % 5 = k % 5 := by omega
  obtain ⟨before, after⟩ := theta_flags (mem.input k)
  have d0 : distance (k % 15) 0 = 1 := rfl
  have d2 : distance (k % 15) 2 = 5 := by simp [distance, high]
  have d12 : distance (k % 15) 12 = [1, 6, 2, 2, 2].getD (k % 5) 0 := by simp [distance, high, column]
  have d14 : distance (k % 15) 14 = [4, 4, 4, 3, 3].getD (k % 5) 0 := by simp [distance, high, column]
  have r0 := g 0 (by decide)
  have r2 := g 2 (by decide)
  have r12 := g 12 (by decide)
  have r14 := g 14 (by decide)
  rw [d0] at r0
  rw [d2] at r2
  rw [d12] at r12
  rw [d14] at r14
  have small : [1, 6, 2, 2, 2].getD (k % 5) 0 ≤ k ∧ [4, 4, 4, 3, 3].getD (k % 5) 0 ≤ k := by
    rcases (by omega : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4) with c | c | c | c | c <;>
      simp only [c, List.getD_cons_zero, List.getD_cons_succ] <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (mem (portKey k 0)).time.1.val + 4 = 1 + 4 * k + 2
    omega
  · show (mem (portKey k 2)).time.1.val + 20 = 1 + 4 * k + 2
    omega
  · rw [before]
    show (mem (portKey k 12)).time.1.val + 4 * [1, 6, 2, 2, 2].getD (k % 5) 0 = 1 + 4 * k + 2
    omega
  · rw [after]
    show (mem (portKey k 14)).time.1.val + 4 * [4, 4, 4, 3, 3].getD (k % 5) 0 = 1 + 4 * k + 2
    omega

theorem chi_clocks (inv : Inv mem k) (call : k < 361) (late : 10 ≤ k % 15) : Chi.Clocks (mem.input k) := by
  have count : portCount k = 12 := by rw [portCount, chi_kind late]; rfl
  have g (j : Nat) (h : j < 12) := grouped inv call (by omega) (j := j) (by rw [count]; exact h)
  have column : k % 15 % 5 = k % 5 := by omega
  have d (j : Nat) (h : 2 ≤ j) : distance (k % 15) j = 5 + k % 5 - (j - 2) / 2 := by
    simp only [distance, show ¬ j < 2 by omega, show ¬ k % 15 < 10 by omega, ↓reduceIte, column]
  have plane : Chi.plane (mem.input k) = k % 5 := rfl
  have r0 := g 0 (by decide)
  have r2 := g 2 (by decide)
  have r4 := g 4 (by decide)
  have r6 := g 6 (by decide)
  have r8 := g 8 (by decide)
  have r10 := g 10 (by decide)
  rw [d 2 (by decide)] at r2
  rw [d 4 (by decide)] at r4
  rw [d 6 (by decide)] at r6
  rw [d 8 (by decide)] at r8
  rw [d 10 (by decide)] at r10
  have d0 : distance (k % 15) 0 = 1 := rfl
  rw [d0] at r0
  have room : 10 ≤ k := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (mem (portKey k 0)).time.1.val + 4 = 1 + 4 * k + 2
    omega
  · rw [plane]
    show (mem (portKey k 2)).time.1.val + 4 * (5 + k % 5) = 1 + 4 * k + 2
    omega
  · rw [plane]
    show (mem (portKey k 4)).time.1.val + 4 * (4 + k % 5) = 1 + 4 * k + 2
    omega
  · rw [plane]
    show (mem (portKey k 6)).time.1.val + 4 * (3 + k % 5) = 1 + 4 * k + 2
    omega
  · rw [plane]
    show (mem (portKey k 8)).time.1.val + 4 * (2 + k % 5) = 1 + 4 * k + 2
    omega
  · rw [plane]
    show (mem (portKey k 10)).time.1.val + 4 * (1 + k % 5) = 1 + 4 * k + 2
    omega

/-- What call `k`'s row does with the memory, by its worker. -/
theorem facts (inv : Inv mem k) (call : k < 361) : RowFacts mem k := by
  by_cases parity : k % 15 < 5
  · exact Parity.row_facts inv call (parity_kind (k := k) parity)
  · by_cases theta : k % 15 < 10
    · refine ThetaRho.row_facts inv call (theta_kind (k := k) (by omega) theta) fun j h => ?_
      rw [grouped inv call (by omega) h, grouped inv call (by omega) (by
        rw [portCount, theta_kind (k := k) (by omega) theta] at h ⊢
        change _ < 16
        split_ifs <;> omega)]
      congr 2
      simp only [distance]
      split_ifs <;> omega
    · refine Chi.row_facts inv call (chi_kind (k := k) (by omega)) fun j h => ?_
      rw [grouped inv call (by omega) h, grouped inv call (by omega) (by
        rw [portCount, chi_kind (k := k) (by omega)] at h ⊢
        change _ < 12
        change j < 12 at h
        split_ifs <;> omega)]
      congr 2
      simp only [distance]
      split_ifs <;> omega

/-- Call `k`'s row satisfies its constraints. -/
theorem holds (inv : Inv mem k) (call : k < 361) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (mem.row k).assignment) (mem.row k).constraints := by
  have valid := valid_of_inv inv call
  by_cases parity : k % 15 < 5
  · have kind := parity_kind (k := k) parity
    rw [Parity.row_eq kind]
    refine Parity.holds (mem.input k) valid kind (fun j h => ?_) rfl
    show (mem (portKey k j)).time.1.val < 1 + 4 * k + 2
    have count : portCount k = 14 := by rw [portCount, kind]; rfl
    rw [previous_eq inv call (portKey_lt (by rw [count]; exact h))]
    have := clock_lt k (portKey k j)
    omega
  · by_cases theta : k % 15 < 10
    · have kind := theta_kind (k := k) (by omega) theta
      rw [ThetaRho.row_eq kind]
      exact ThetaRho.holds (mem.input k) valid kind (theta_clocks inv call (by omega) theta) rfl
    · have kind := chi_kind (k := k) (by omega)
      rw [Chi.row_eq kind]
      exact Chi.holds (mem.input k) valid kind (chi_clocks inv call (by omega)) rfl

end Airbender.NonVacuous.KeccakSplitSpan
