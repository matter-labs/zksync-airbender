import Human.Circuits.AddSub.RVModel
import Slop.Trace.RVPooledRow

/-! RV32 AddSub pilot, history side: for an accepted ADD/SUB/ADDI/LUI/AUIPC row and any RV pre-state at which the row
    sits (`RVRowPosition`), the row's two operand registers hold the values the row read.

    The row's RV history is the family-agnostic `rv_pooled_row_history`; its x0 and writable-store laws are derived
    on the RV route (`rv_pooled_zero_writes`, `rv_pooled_writable`). -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace Trace.Proofs

theorem rv_addsub_row_position {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (assumptions : RVInterfaceAssumptions trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {before : RV.State} (position : RVRowPosition trace initial cells (⟨.addSub, w⟩ : Row p PooledFamily) before) :
    ∀ i j : BitVec 5, w 5 = (i.toNat : ZMod p) → w 6 = (j.toNat : ZMod p) →
      before.getReg i = memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) ∧
      before.getReg j = memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) := by
  obtain ⟨middle, events, rawAfter, _, _, current, atState, _⟩ :=
    rv_pooled_row_history hp inverse accepted assumptions.toRVPooledHistoryInputs decoded position
  intro i j hi hj
  have shape : (⟨.addSub, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.addSub, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := rfl
    rw [portsEq]
    first
      | rfl
      | simp [importedConstraintsMemoryPorts]
  have boundP : 32 ≤ p := by
    dsimp [timestampBase] at hp
    omega
  have valueLeft : (w 5).val = i.toNat := by
    rw [hi, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have valueRight : (w 6).val = j.toNat := by
    rw [hj, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  dsimp only [rowEvents] at current
  rw [shape] at current
  have leftAddress : (importedConstraintsMemoryPorts[0]).address.code w =
      (Cell.register i).addressCode := by
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, valueLeft]
  have rightAddress : (importedConstraintsMemoryPorts[1]).address.code w =
      (Cell.register j).addressCode := by
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, valueRight]
  have firstReadonly : (importedConstraintsMemoryPorts[0]).writeValue = none := by
    simp [importedConstraintsMemoryPorts]
  have operands := rv_row_operand_reads trace.memoryEpoch firstReadonly leftAddress rightAddress current
  subst atState
  exact operands

end Airbender.AddSub.Proofs
