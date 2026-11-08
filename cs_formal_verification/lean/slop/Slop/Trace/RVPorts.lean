module
public import Slop.Trace.RVHistory
public import Slop.ISA.RV.Mem
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! The RV history of one row with three ports, the first two read-only (operand reads, then a destination
    read/write): both reads see the pre-state, the third port's update gives the post-state. -/

namespace Airbender.Trace.Proofs
open Arithmetic

theorem rv_three_ports {p : Nat} {cells : List Cell} {columns : TraceColumns}
    {first second destination : MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {before after : RV.State}
    (history : RVHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    ∃ c0 ∈ cells, ∃ c1 ∈ cells, ∃ c2 ∈ cells,
      c0.addressCode = first.address.code w ∧ c0.readRV before = some (memoryWord (first.readCode w)) ∧
      c1.addressCode = second.address.code w ∧ c1.readRV before = some (memoryWord (second.readCode w)) ∧
      c2.addressCode = destination.address.code w ∧
      c2.readRV before = some (memoryWord (destination.readCode w)) ∧
      c2.applyRV (memoryWord (destination.writeCode w)) before = some after := by
  have firstSame : first.writeCode w = first.readCode w := by
    simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly]
  have secondSame : second.writeCode w = second.readCode w := by
    simp [MemoryPort.readCode, MemoryPort.writeCode, secondReadonly]
  dsimp [nativeRowEvents] at history
  cases history with
  | cons past c2 m2 a2 r2 w2 =>
    cases past with
    | cons past c1 m1 a1 r1 w1 =>
      cases past with
      | cons empty c0 m0 a0 r0 w0 =>
        cases empty with
        | nil =>
          have keep0 := (show ∀ s : RV.State, c0.readRV s = some (memoryWord (first.readCode w)) →
              c0.applyRV (memoryWord (first.writeCode w)) s = some s from
            fun s r => by rw [firstSame]; simp [Cell.applyRV, r]) _ r0
          have e0 := Option.some.inj (w0.symm.trans keep0)
          subst e0
          have keep1 := (show ∀ s : RV.State, c1.readRV s = some (memoryWord (second.readCode w)) →
              c1.applyRV (memoryWord (second.writeCode w)) s = some s from
            fun s r => by rw [secondSame]; simp [Cell.applyRV, r]) _ r1
          have e1 := Option.some.inj (w1.symm.trans keep1)
          subst e1
          exact ⟨c0, m0, c1, m1, c2, m2, a0, r0, a1, r1, a2, r2, w2⟩

/-- A word write of the word already stored changes nothing. -/
theorem rv_write_read_self (m : RV.Word → BitVec 8) (a : RV.Word) : RV.write m a (RV.read m a 4) 4 = m := by
  funext b
  by_cases inside : ∃ k : Nat, k < 4 ∧ b = a + BitVec.ofNat 32 k
  · obtain ⟨k, small, rfl⟩ := inside
    have h1 : a + 1 ≠ a := by bv_omega
    have h2 : a + 1 + 1 ≠ a := by bv_omega
    have h3 : a + 1 + 1 + 1 ≠ a := by bv_omega
    have h4 : a + 1 + 1 ≠ a + 1 := by bv_omega
    have h5 : a + 1 + 1 + 1 ≠ a + 1 := by bv_omega
    have h6 : a + 1 + 1 + 1 ≠ a + 1 + 1 := by bv_omega
    have e0 : a + BitVec.ofNat 32 0 = a := by bv_omega
    have e1 : a + BitVec.ofNat 32 1 = a + 1 := by bv_omega
    have e2 : a + BitVec.ofNat 32 2 = a + 1 + 1 := by bv_omega
    have e3 : a + BitVec.ofNat 32 3 = a + 1 + 1 + 1 := by bv_omega
    interval_cases k <;> simp only [e0, e1, e2, e3, RV.write, RV.read] <;>
      simp only [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm,
        ite_true, ite_false] <;>
      ext i hi <;>
      simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, hi,
        show i < 32 by omega, show 8 + i < 32 by omega, show 16 + i < 32 by omega, show 24 + i < 32 by omega,
        show 16 + i - 8 = 8 + i by omega, show 8 + i - 8 = i by omega, show 24 + i - 8 = 16 + i by omega,

        show ¬ 8 + i < 8 by omega, show ¬ 16 + i < 8 by omega,
        show ¬ 24 + i < 8 by omega, show 8 ≤ 16 + i by omega, show 8 ≤ 8 + i by omega, show 8 ≤ 24 + i by omega]
  · apply RV.write_other
    intro i hi same
    exact inside ⟨i, hi, same⟩

end Airbender.Trace.Proofs
