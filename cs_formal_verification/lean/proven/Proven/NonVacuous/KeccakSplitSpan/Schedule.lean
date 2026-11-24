module
public import Proven.NonVacuous.KeccakSplitSpan.Common

@[expose] public section

/-! The schedule's slots, round by round: call `k`'s slot at a lane position is the round's slot map
    (`Call.physicalSlot (k / 15)`) applied to a logical slot that depends only on the call's position `k % 15` in its
    round (chi's row after pi is `piSource` of the next round's coordinates); the parity slots are fixed. The round's
    map is injective, so which call last touched a key within a round is a fact about the fifteen positions, decided
    once (`Logical.lean`), instead of a fact about all 361 calls. -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Keccak.Split Keccak.Split.SetupProofs

/-- A slot in round `r`: a state lane through the round's slot map; parity and unused slots are fixed. -/
def roundSlot (r s : Nat) : Nat := if h : s < 25 then (Call.physicalSlot r ⟨s, h⟩).val else s

/-- `Call.piSource` on slot numbers. -/
def piSlot (s : Nat) : Nat := (s % 5 + 3 * (s / 5)) % 5 + 5 * (s % 5)

/-- The logical slot at lane position `pos` of the call at position `c` of a round. -/
def logicalSlot (c pos : Nat) : Nat :=
  if pos < 5 then
    if c < 10 then c % 5 + 5 * pos
    else piSlot (5 * (c % 5) + (pos + 2 * (c % 5)) % 5)
  else if c < 5 ∧ pos = 5 then 25 + c % 5
  else if 5 ≤ c ∧ c < 10 then 25 + (if pos = 5 then (c % 5 + 4) % 5 else (c % 5 + 1) % 5)
  else 30

/-- A memory key in round `r`, and the logical key of port `j` of the call at position `c`. -/
def roundKey (r key : Nat) : Nat := if key < 2 then key else 2 + 2 * roundSlot r ((key - 2) / 2) + (key - 2) % 2

def logicalKey (c j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then 1 else 2 + 2 * logicalSlot c ((j - 2) / 2) + (j - 2) % 2

/-- The ports of the call at position `c`: parity six lanes, theta+rho seven, chi five. -/
def logicalCount (c : Nat) : Nat := if c < 5 then 14 else if c < 10 then 16 else 12

def logicalKeys (c : Nat) : List Nat := (List.range (logicalCount c)).map (logicalKey c)

theorem kindAt_eq (k : Nat) :
    kindAt k = if k % 15 < 5 then .columnParity else if k % 15 < 10 then .thetaRho else .chi5 := by
  unfold kindAt
  split_ifs <;> first | rfl | omega

theorem portCount_eq (k : Nat) : portCount k = logicalCount (k % 15) := by
  unfold portCount logicalCount
  rw [kindAt_eq k]
  split_ifs <;> rfl

theorem physicalSlot_val (r : Nat) (l : Fin 25) : (Call.physicalSlot r l).val = roundSlot r l.val := by
  unfold roundSlot
  simp only [l.isLt, ↓reduceDIte]

/-- The next round's map is this round's after pi. -/
theorem roundSlot_succ (r : Nat) {s : Nat} (lane : s < 25) : roundSlot (r + 1) s = roundSlot r (piSlot s) := by
  have inside : piSlot s < 25 := by unfold piSlot; omega
  unfold roundSlot
  simp only [lane, inside, ↓reduceDIte]
  rfl

theorem slotNat_eq (k pos : Nat) :
    slotNat k pos = roundSlot (k / 15) (logicalSlot (k % 15) pos) := by
  have column : k % 15 % 5 = k % 5 := by omega
  unfold slotNat logicalSlot
  rw [kindAt_eq k]
  simp only [physicalSlot_val, column]
  by_cases first : pos < 5
  · rw [roundSlot_succ _ (by omega)]
    by_cases parity : k % 15 < 5
    · simp only [first, parity, show k % 15 < 10 by omega, ↓reduceDIte, ↓reduceIte, reduceCtorEq]
    · by_cases theta : k % 15 < 10
      · simp only [first, parity, theta, ↓reduceDIte, ↓reduceIte, reduceCtorEq]
      · simp only [first, parity, theta, ↓reduceDIte, ↓reduceIte]
  · have parked (s : Nat) (h : 25 ≤ s) : roundSlot (k / 15) s = s := by
      unfold roundSlot
      simp only [show ¬ s < 25 by omega, ↓reduceDIte]
    simp only [first, ↓reduceDIte, ↓reduceIte]
    by_cases parity : k % 15 < 5
    · simp only [parity, show k % 15 < 10 by omega, ↓reduceIte, true_and, reduceCtorEq]
      split_ifs <;> rw [parked _ (by omega)]
      omega
    · by_cases theta : k % 15 < 10
      · simp only [parity, theta, ↓reduceIte, reduceCtorEq, false_and, and_true, show 5 ≤ k % 15 by omega]
        split_ifs <;> rw [parked _ (by omega)]
      · simp only [parity, theta, ↓reduceIte, reduceCtorEq, false_and, and_false]
        rw [parked _ (by omega)]

end Airbender.NonVacuous.KeccakSplitSpan
