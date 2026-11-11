module
public import Slop.NonVacuous.Blake2RoundSpan.AssertEval

@[expose] public section

/-! Imported constraints of an honest round row (the last 24 preparation equations: prepared lanes 6 to 15 (the first round reads the chaining state and the IV)): each holds for the honest assignment of valid inputs. -/

namespace Airbender.NonVacuous.Blake2RoundSpan

variable {p : Nat} [Fact p.Prime] {x : RowInput}

private theorem assert_28 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 28) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_28]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_29 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 29) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_29]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_30 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 30) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_30]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_31 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 31) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_31]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_32 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 32) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_32]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_33 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 33) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_33]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_34 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 34) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_34]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_35 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 35) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_35]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_36 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 36) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_36]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_37 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 37) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_37]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_38 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 38) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_38]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_39 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 39) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_39]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_40 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 40) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_40]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_41 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 41) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_41]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_42 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 42) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_42]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_43 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 43) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_43]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_44 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 44) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_44]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_45 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 45) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_45]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_46 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 46) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_46]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_47 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 47) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_47]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_48 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 48) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_48]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_49 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 49) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_49]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_50 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 50) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_50]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

private theorem assert_51 {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 51) : (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL index
  rw [Blake2Round.importedConstraints.constraint_51]
  simp only [Expression.eval, Verification.environment, RowInput.assignment]
  honest_value
  first_round_cases x

theorem asserts_Lanes {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (range : (28 ≤ n ∧ n ≤ 51)) :
    (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  rcases (by omega : n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨ n = 50 ∨ n = 51) with
    index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index
  · exact assert_28 hL index
  · exact assert_29 hL index
  · exact assert_30 hL index
  · exact assert_31 hL index
  · exact assert_32 hL index
  · exact assert_33 hL index
  · exact assert_34 hL index
  · exact assert_35 hL index
  · exact assert_36 hL index
  · exact assert_37 hL index
  · exact assert_38 hL index
  · exact assert_39 hL index
  · exact assert_40 hL index
  · exact assert_41 hL index
  · exact assert_42 hL index
  · exact assert_43 hL index
  · exact assert_44 hL index
  · exact assert_45 hL index
  · exact assert_46 hL index
  · exact assert_47 hL index
  · exact assert_48 hL index
  · exact assert_49 hL index
  · exact assert_50 hL index
  · exact assert_51 hL index

end Airbender.NonVacuous.Blake2RoundSpan
