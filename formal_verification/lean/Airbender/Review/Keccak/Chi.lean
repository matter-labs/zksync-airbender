import Airbender.Review.Keccak.Theta

namespace Airbender.Keccak

/-- The two native Chi modes split one five-lane row across two calls.
    `first` reads state columns 1–4. `second` reads column 0 and the preserved
    columns 3–4, then consumes the two scratch writes from `first`.
    These equalities bind actual memory reads; no Chi result or range is assumed.
    Controller scheduling and global memory transport remain separate obligations. -/
structure ChiMapping {p : Nat} (state : Vector Nat 25) (row : Fin 5)
    (first second : Nat → ZMod p) : Prop where
  firstActive : first Variables.execute = 1
  firstSelected : first Variables.modeColumns[(5 : Fin 7)] = 1
  secondActive : second Variables.execute = 1
  secondSelected : second Variables.modeColumns[(6 : Fin 7)] = 1
  firstState : ∀ i : Fin 4,
    readLane first ⟨i.val, by omega⟩ = state[5 * (i.val + 1) + row.val]
  secondState : readLane second 0 = state[row.val]
  preservedState : ∀ i : Fin 2,
    readLane second ⟨i.val + 1, by omega⟩ = writeLane first ⟨i.val + 2, by omega⟩
  scratch : readLane second 3 = writeLane first 4 ∧
    readLane second 4 = writeLane first 5

/-- The five state writes produced by the two native calls, in Clean's
    column order. Numeric port placement stays in `readLane`/`writeLane`. -/
def chiWrites {p : Nat} (first second : Nat → ZMod p) : Vector Nat 5 :=
  #v[writeLane second 0, writeLane first 0, writeLane first 1,
    writeLane second 1, writeLane second 2]

/-- All five state writes match one row of Clean's original Chi reference.
    The first call preserves its last two state reads; the second preserves
    its three scratch reads. Other rows and call scheduling are not claimed. -/
def ChiResult {p : Nat} (state : Vector Nat 25) (row : Fin 5)
    (first second : Nat → ZMod p) : Prop :=
  (∀ i : Fin 5, (chiWrites first second)[i] =
    (Specs.Keccak256.chi state)[5 * i.val + row.val]) ∧
  (∀ i : Fin 2, writeLane first ⟨i.val + 2, by omega⟩ = readLane first ⟨i.val + 2, by omega⟩) ∧
  (∀ i : Fin 3, writeLane second ⟨i.val + 3, by omega⟩ = readLane second ⟨i.val + 3, by omega⟩)

end Airbender.Keccak
