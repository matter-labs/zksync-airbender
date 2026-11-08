module
public import Human.Circuits.AddSub.RVModel
public import Slop.Trace.RVPooledRow
public import Slop.Trace.RVRowGlue

@[expose] public section

/-! RV32 AddSub pilot, history side: for an accepted ADD/SUB/ADDI/LUI/AUIPC row and any RV pre-state at which the row
    sits (`RVRowPosition`), the row's two operand registers hold the values the row read.

    The row's RV history is the family-agnostic `rv_pooled_row_history`; its x0 and writable-store laws are derived
    on the RV route (`rv_pooled_zero_writes`, `rv_pooled_writable`). -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace Trace.Proofs

theorem rv_addsub_row_position (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    (assumptions : RVInterfaceAssumptions trace initial cells program)
    (decoded : RVPooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {before : RV.State} (position : RVRowPosition trace initial cells (⟨.addSub, w⟩ : Row p PooledFamily) before) :
    ∀ i j : BitVec 5, w 5 = (i.toNat : ZMod p) → w 6 = (j.toNat : ZMod p) →
      before.getReg i = memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) ∧
      before.getReg j = memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) := by
  intro i j hi hj
  have shape : (⟨.addSub, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.addSub, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    first
      | rfl
      | simp [importedConstraintsMemoryPorts]
  have operands := rv_row_register_reads laws hp inverse accepted assumptions.toRVPooledHistoryInputs decoded position shape
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6)
    (by first | rfl | simp [importedConstraintsMemoryPorts])
    (by first | rfl | simp [importedConstraintsMemoryPorts]) hi hj
  exact operands

end Airbender.AddSub.Proofs
