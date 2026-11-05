import Human.Circuits.AddSub.RVModel
import Slop.Trace.RVHistory

/-! RV32 AddSub pilot, history side: from the RV interface assumptions and an accepted ADD/SUB/ADDI/LUI/AUIPC row,
    the row has an RV pre-state (`RVRowPosition`), and its two operand registers hold the values the row read.

    Two hypotheses are explicit, not derived here: the x0 law on native writes (`zero`: a write to x0 carries 0, which
    the decoder/x0 preprocessing of the row family must supply) and the writable-store law (`writable`: a store lands
    in RAM, which the word/subword store trap enforces for the row's store family). -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace Trace.Proofs

theorem rv_addsub_row_position {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} (accepted : Accepted trace)
    {initial : RV.State} {cells : List Cell} {program : List PooledProgramEntry}
    (assumptions : RVInterfaceAssumptions trace initial cells program)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0)
    (writable : ∀ event ∈ trace.nativeEvents, ∀ cell ∈ cells, cell.addressCode = event.2.1 →
      ∀ index, cell = .ram index → RV.writable index 4) :
    ∃ before, RVRowPosition trace initial cells (⟨.addSub, w⟩ : Row p PooledFamily) before ∧
      ∀ i j : BitVec 5, w 5 = (i.toNat : ZMod p) → w 6 = (j.toNat : ZMod p) →
        before.getReg i = memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) ∧
        before.getReg j = memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) := by
  have clocks := assumptions.initialization.clocks
  obtain ⟨history, rows, after, _, rowsPermutation, rowsOrdered, native, _⟩ :=
    rv_native_row_history hp inverse accepted clocks assumptions.initialization.image
      assumptions.initialization.distinct assumptions.initialization.aligned zero writable
  have projection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection (by dsimp [timestampBase] at hp; omega) inverse accepted clocks]
    exact rowsPermutation.flatMap (fun row _ => List.reverse_perm _)
  obtain ⟨before, position⟩ := rv_row_position_of_history rowsPermutation rowsOrdered native member
  obtain ⟨middle, events, rawAfter, _, _, current, atState⟩ :=
    rv_row_context_of_history rowsPermutation rowsOrdered native projection position
  refine ⟨before, position, ?_⟩
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
