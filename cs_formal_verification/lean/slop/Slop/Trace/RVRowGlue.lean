import Slop.Trace.RVPooledRow

/-! Family-agnostic glue shared by the per-family RV trace proofs (proved once, cited by each family):

    - `rv_same_of_write` / `rv_same_of_store`: `RV.Same` of the one-step result and the claimed post-state.
    - `register_address_code`: a register-column port addresses the register its column names.
    - `rv_row_register_reads`: the two operand ports of a pooled row (register columns `a`, `b`) read the pre-state
      registers, from `rv_pooled_row_history` and `rv_row_operand_reads`. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Register/PC agreement of one step that writes `x` to `rd` with the claimed post-state (`x` and `out` need only
    agree when `rd` is not x0). -/
theorem rv_same_of_write (s : RV.State) (rd : RV.Reg) (x out pc : BitVec 32)
    (value : rd ≠ 0 → x = out) (hpc : s.pc + 4 = pc) :
    RV.Same (s.setReg rd x).nextInstr ((s.setReg rd out).setPC pc) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simpa [RV.State.nextInstr, RV.State.setPC, RV.State.setReg] using hpc
  · intro i
    simp only [RV.State.getReg, RV.State.nextInstr, RV.State.setPC, RV.State.setReg]
    by_cases hi : i = 0
    · simp [hi]
    · by_cases hr : i = rd
      · subst hr
        simp [value hi]
      · simp [hr]

/-- Agreement of a step that stores `x` at `a` with the claimed post-state. -/
theorem rv_same_of_store (s : RV.State) (a x out pc : BitVec 32)
    (value : x = out) (hpc : s.pc + 4 = pc) :
    RV.Same (s.store a x 4).nextInstr ((s.store a out 4).setPC pc) := by
  subst value
  subst hpc
  exact ⟨rfl, fun _ => rfl, rfl, rfl⟩

/-- A register-column port whose column holds `i` addresses register `i`. -/
theorem register_address_code {p : Nat} (hp : 32 ≤ p) {w : Nat → ZMod p} {column : Nat} {i : BitVec 5}
    (value : w column = (i.toNat : ZMod p)) :
    (MemoryAddress.register column).code w = (Cell.register i).addressCode := by
  have hv : (w column).val = i.toNat := by
    rw [value, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  simp [MemoryAddress.code, Cell.addressCode, hv]

/-- The two operand ports of a pooled row read the pre-state registers their columns name. -/
theorem rv_row_register_reads (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (inputs : RVPooledHistoryInputs trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {row : Row p PooledFamily} {before : RV.State}
    (position : RVRowPosition trace initial cells row before)
    {first second destination : MemoryPort} (shape : row.ports = #[first, second, destination])
    (firstReadonly : first.writeValue = none) {a b : Nat}
    (firstAt : first.address = .register a) (secondAt : second.address = .register b)
    {i j : BitVec 5} (hi : row.assignment a = (i.toNat : ZMod p)) (hj : row.assignment b = (j.toNat : ZMod p)) :
    before.getReg i = memoryWord (first.readCode row.assignment) ∧
      before.getReg j = memoryWord (second.readCode row.assignment) := by
  obtain ⟨middle, events, rawAfter, _, _, current, atState, _⟩ :=
    rv_pooled_row_history laws hp inverse accepted inputs decoded position
  have boundP : 32 ≤ p := by
    dsimp [timestampBase] at hp
    omega
  dsimp only [rowEvents] at current
  rw [shape] at current
  have leftAddress : first.address.code row.assignment = (Cell.register i).addressCode := by
    rw [firstAt]; exact register_address_code boundP hi
  have rightAddress : second.address.code row.assignment = (Cell.register j).addressCode := by
    rw [secondAt]; exact register_address_code boundP hj
  have operands := rv_row_operand_reads trace.memoryEpoch firstReadonly leftAddress rightAddress current
  subst atState
  exact operands

end Airbender.Trace.Proofs
