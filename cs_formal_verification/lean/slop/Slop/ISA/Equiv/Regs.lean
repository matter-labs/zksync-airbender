import Human.ISA.Sail.Theorems
import Slop.ISA.Sail.Monad
import Mathlib.Tactic.IntervalCases

/-! Sail's integer registers on an `SailState`, proven once: reading `x i` gives `xget σ i` (0 for x0), writing
gives `xset σ i v` (no change for x0). Every instruction proof reuses these. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

/-- Sail's `x i` (`i ≠ 0`). -/
def xget (σ : SailState) (i : BitVec 5) : BitVec 32 :=
  match i.toNat with
  | 0 => 0
  | 1 => σ.regs .x1
  | 2 => σ.regs .x2
  | 3 => σ.regs .x3
  | 4 => σ.regs .x4
  | 5 => σ.regs .x5
  | 6 => σ.regs .x6
  | 7 => σ.regs .x7
  | 8 => σ.regs .x8
  | 9 => σ.regs .x9
  | 10 => σ.regs .x10
  | 11 => σ.regs .x11
  | 12 => σ.regs .x12
  | 13 => σ.regs .x13
  | 14 => σ.regs .x14
  | 15 => σ.regs .x15
  | 16 => σ.regs .x16
  | 17 => σ.regs .x17
  | 18 => σ.regs .x18
  | 19 => σ.regs .x19
  | 20 => σ.regs .x20
  | 21 => σ.regs .x21
  | 22 => σ.regs .x22
  | 23 => σ.regs .x23
  | 24 => σ.regs .x24
  | 25 => σ.regs .x25
  | 26 => σ.regs .x26
  | 27 => σ.regs .x27
  | 28 => σ.regs .x28
  | 29 => σ.regs .x29
  | 30 => σ.regs .x30
  | _ => σ.regs .x31

/-- Set Sail's `x i` (no change for `i = 0`). -/
def xset (σ : SailState) (i : BitVec 5) (v : BitVec 32) : SailState :=
  match i.toNat with
  | 0 => σ
  | 1 => σ.set .x1 v
  | 2 => σ.set .x2 v
  | 3 => σ.set .x3 v
  | 4 => σ.set .x4 v
  | 5 => σ.set .x5 v
  | 6 => σ.set .x6 v
  | 7 => σ.set .x7 v
  | 8 => σ.set .x8 v
  | 9 => σ.set .x9 v
  | 10 => σ.set .x10 v
  | 11 => σ.set .x11 v
  | 12 => σ.set .x12 v
  | 13 => σ.set .x13 v
  | 14 => σ.set .x14 v
  | 15 => σ.set .x15 v
  | 16 => σ.set .x16 v
  | 17 => σ.set .x17 v
  | 18 => σ.set .x18 v
  | 19 => σ.set .x19 v
  | 20 => σ.set .x20 v
  | 21 => σ.set .x21 v
  | 22 => σ.set .x22 v
  | 23 => σ.set .x23 v
  | 24 => σ.set .x24 v
  | 25 => σ.set .x25 v
  | 26 => σ.set .x26 v
  | 27 => σ.set .x27 v
  | 28 => σ.set .x28 v
  | 29 => σ.set .x29 v
  | 30 => σ.set .x30 v
  | _ => σ.set .x31 v

theorem rX_run (i : BitVec 5) (σ : SailState) : runSail (rX_bits (.Regidx i)) σ = .ok (xget σ i) σ := by
  obtain ⟨⟨n, hn⟩⟩ := i
  interval_cases n <;> rfl

theorem wX_run (i : BitVec 5) (v : BitVec 32) (σ : SailState) : runSail (wX_bits (.Regidx i) v) σ = .ok () (xset σ i v) := by
  obtain ⟨⟨n, hn⟩⟩ := i
  interval_cases n <;> rfl

theorem reg_eq (σ : SailState) (i : BitVec 5) : Airbender.getReg σ i = xget σ i := by
  unfold Airbender.getReg; rw [rX_run]

theorem xget_zero (σ : SailState) : xget σ 0 = 0 := rfl

theorem xset_mem (σ : SailState) (i : BitVec 5) (v : BitVec 32) : (xset σ i v).mem = σ.mem := by
  obtain ⟨⟨n, hn⟩⟩ := i
  interval_cases n <;> rfl

/-- `xset` touches only x1..x31: the PC, `nextPC` and every non-volatile register are unchanged. -/
theorem xset_regs (σ : SailState) (i : BitVec 5) (v : BitVec 32) (r : Register)
    (hr : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧
      r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 ∧ r ≠ .x18 ∧ r ≠ .x19 ∧
      r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x25 ∧ r ≠ .x26 ∧ r ≠ .x27 ∧ r ≠ .x28 ∧
      r ≠ .x29 ∧ r ≠ .x30 ∧ r ≠ .x31) :
    (xset σ i v).regs r = σ.regs r := by
  obtain ⟨⟨n, hn⟩⟩ := i
  interval_cases n <;> simp_all [xset, SailState.set, eq_comm]

theorem xget_xset (σ : SailState) (i j : BitVec 5) (v : BitVec 32) :
    xget (xset σ i v) j = if j = 0 then 0 else if j = i then v else xget σ j := by
  obtain ⟨⟨n, hn⟩⟩ := i
  obtain ⟨⟨m, hm⟩⟩ := j
  interval_cases n <;> interval_cases m <;> rfl

end Slop.Equiv
