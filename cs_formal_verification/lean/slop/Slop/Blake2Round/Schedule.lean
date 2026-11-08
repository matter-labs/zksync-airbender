module
public import Slop.Blake2Round.ArtifactChecks
public import Slop.Blake2Round.OpIndex
public import Slop.Blake2G.OpIndex
public import Human.Circuits.Blake2Round.Schedule
public import Slop.Constraints
public import Slop.Templates
public import Slop.Arithmetic.Lemmas
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Schedule.Proofs
open Arithmetic Templates
open scoped BigOperators

def column (round : Fin 10) (position : Fin 16) : Fin 16 :=
  Fin.ofNat 16 Blake2G.Control.messageSchedule[round][position]

/-! The imported equations, as data. Constraint `54 + r` (`64 + r`) is the product
`w (204 + r) = w (142 + r) * w 203` (`w (214 + r) = w (142 + r) * w 202`) of round bit `r`
and a mode column; constraint `74 + 2 j + limb` sums, round by round, the terms of
`Preparation.messageLimb` for message word `column r j`, over the committed products.
`products_shape` and `message_shape` check the imported constraints against these
templates, one closed fact per index; `products`, `round_terms` and `round_sum` evaluate the
templates once. The expression nodes (`constant`, `product`, `minus`, `cell`) are `Templates`'. -/

/-- Constraint `bit * mode - out`. -/
def productConstraint {p : Nat} (bit mode out : Nat) : Expression (ZMod p) :=
  minus ((constant (Int.ofNat 0)).add (product (cell bit) (cell mode))) (cell out)

/-- The terms of round `r` for message word `word`, added to `sum`. -/
def roundTerms {p : Nat} (sum : Expression (ZMod p)) (r word limb : Nat) : Expression (ZMod p) :=
  let bit := (constant (Int.ofNat 0)).add (cell (142 + r))
  if word < 8 then
    (sum.add (product (minus bit (cell (204 + r))) (cell (103 + 2 * word + limb)))).add
      (product (cell (204 + r)) (cell (5 + 4 * word + limb)))
  else
    ((sum.add (product (minus (minus bit (cell (204 + r))) (cell (214 + r)))
        (cell (103 + 2 * word + limb)))).add
      (product (cell (214 + r)) (cell (5 + 4 * (word - 8) + limb)))).add
      (product (cell (204 + r)) (cell (103 + 2 * (word - 8) + limb)))

/-- The terms of the first `n` rounds for scheduled word `j`. -/
def roundSum {p : Nat} (j : Fin 16) (limb : Nat) : Nat → Expression (ZMod p)
  | 0 => constant (Int.ofNat 0)
  | n + 1 => if h : n < 10 then roundTerms (roundSum j limb n) n (column ⟨n, h⟩ j).val limb
      else roundSum j limb n

/-- Constraint `74 + 2 j + limb`. -/
def messageConstraint {p : Nat} (j : Fin 16) (limb : Nat) : Expression (ZMod p) :=
  minus (roundSum j limb 10) (cell (224 + 2 * j.val + limb))

theorem products_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) (r : Fin 10) :
    (FlatOperation.constraints (importedConstraints setup)).get
        ⟨54 + r.val, by rw [constraint_count]; omega⟩ =
      productConstraint (142 + r.val) 203 (204 + r.val) ∧
    (FlatOperation.constraints (importedConstraints setup)).get
        ⟨64 + r.val, by rw [constraint_count]; omega⟩ =
      productConstraint (142 + r.val) 202 (214 + r.val) := by
  fin_cases r <;> op_index <;> exact ⟨rfl, rfl⟩

theorem message_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) (j : Fin 16)
    (limb : Fin 2) :
    (FlatOperation.constraints (importedConstraints setup)).get
        ⟨74 + 2 * j.val + limb.val, by rw [constraint_count]; omega⟩ =
      messageConstraint j limb.val := by
  fin_cases j <;> fin_cases limb <;> op_index <;> rfl

/-- The products of the round bits with the two mode columns. -/
theorem products {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (r : Nat) (hr : r < 10) :
    w (204 + r) = w (142 + r) * w 203 ∧ w (214 + r) = w (142 + r) * w 202 := by
  have shape := products_shape setup ⟨r, hr⟩
  have left := Verification.assertion_of_holds h ⟨54 + r, by rw [constraint_count]; omega⟩
  have right := Verification.assertion_of_holds h ⟨64 + r, by rw [constraint_count]; omega⟩
  rw [shape.1] at left
  rw [shape.2] at right
  simp only [productConstraint, Expression.eval, Verification.environment] at left right
  push_cast at left right
  constructor
  · linear_combination -left
  · linear_combination -right

/-- One round's terms evaluate to the round bit times the selected message limb. -/
theorem round_terms {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} (sum : Expression (ZMod p))
    (r word limb : Nat)
    (p203 : w (204 + r) = w (142 + r) * w 203) (p202 : w (214 + r) = w (142 + r) * w 202) :
    (roundTerms sum r word limb).eval (Verification.environment w) =
      sum.eval (Verification.environment w) +
        w (142 + r) * Preparation.messageLimb w word limb := by
  unfold roundTerms Preparation.messageLimb
  split_ifs <;>
    simp only [Expression.eval, Verification.environment] <;>
    push_cast <;> rw [p203] <;> (try rw [p202]) <;> ring

theorem round_sum {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (products : ∀ r < 10, w (204 + r) = w (142 + r) * w 203 ∧ w (214 + r) = w (142 + r) * w 202)
    (j : Fin 16) (limb : Nat) (n : Nat) (hn : n ≤ 10) :
    (roundSum j limb n).eval (Verification.environment w) =
      ∑ r : Fin n, w (142 + r.val) *
        Preparation.messageLimb w (column ⟨r.val, by omega⟩ j).val limb := by
  induction n with
  | zero => simp [roundSum, constant_eval]
  | succ n ih =>
    have hn' : n < 10 := by omega
    simp only [roundSum, hn', ↓reduceDIte]
    rw [round_terms _ _ _ _ (products n hn').1 (products n hn').2, ih (by omega),
      Fin.sum_univ_castSucc]
    rfl

/-- Normalize each imported equation once to a sum over rounds of the selected
    (uncommitted) message limb. The round×mode products 204..223 (constraints
    54..73) are substituted first. The exclusive mask is used only afterward;
    the circuit's multi-selector behavior is retained. -/
theorem equations {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ j : Fin 16,
      w Variables.scheduledMessage[j].1 = ∑ r : Fin 10,
        w Variables.roundBits[r] * Preparation.messageLimb w (column r j).val 0 ∧
      w Variables.scheduledMessage[j].2 = ∑ r : Fin 10,
        w Variables.roundBits[r] * Preparation.messageLimb w (column r j).val 1 := by
  have bits : ∀ r : Fin 10, Variables.roundBits[r] = 142 + r.val := by decide
  intro j
  have limb (l : Fin 2) : w (224 + 2 * j.val + l.val) = ∑ r : Fin 10,
      w Variables.roundBits[r] * Preparation.messageLimb w (column r j).val l.val := by
    have zero := Verification.assertion_of_holds h
      ⟨74 + 2 * j.val + l.val, by rw [constraint_count]; omega⟩
    rw [message_shape setup j l, messageConstraint, Expression.eval, Expression.eval,
      round_sum (products h) j l.val 10 le_rfl] at zero
    simp only [bits, Expression.eval, Verification.environment] at zero ⊢
    push_cast at zero
    linear_combination -zero
  have high := limb 1
  rw [show 224 + 2 * j.val + (1 : Fin 2).val = 225 + 2 * j.val by simp only [Fin.val_one]; omega]
    at high
  constructor
  · simpa [Variables.scheduledMessage] using limb 0
  · simpa [Variables.scheduledMessage] using high

theorem soundness {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨interface, h, mapping⟩
  have fields := equations h
  have selected (f : Fin 10 → ZMod p) : (∑ r, w Variables.roundBits[r] * f r) = f input.round := by
    calc
      _ = ∑ r : Fin 10, (if r = input.round then 1 else 0) * f r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [interface.roundMask r]
      _ = _ := by simp
  unfold spec step
  rw [mapping.output, mapping.message]
  apply Vector.ext
  intro j hj
  obtain ⟨lo, high⟩ := fields ⟨j, hj⟩
  rw [selected] at lo high
  simp only [Fin.getElem_fin] at lo high
  simp only [Preparation.words, Preparation.messageWords, Vector.getElem_map]
  rw [lo, high]
  simp only [column, Fin.getElem_fin, Vector.getElem_ofFn]

end Airbender.Blake2Round.Schedule.Proofs
