module
public import Human.Helpers.Context.RVInterfaces
public import Slop.Trace.RVPorts
public import Slop.Trace.RVCells
public import Slop.Trace.RVRowGlue
public import Slop.Trace.InitialImage
public import Slop.ISA.RV.Same

@[expose] public section

/-! The per-row obligation of the six-family RV composition, stated from the row's own RV history (not from the
    whole-trace interface, so it holds for any decoder projection): `RVPooledRowStep` (the row's instruction executes
    from the row's pre-state to a state agreeing with the row's history followed by its final PC), and what the trace
    gives for one row (`RVPooledRowFacts`). Glue shared by the family lemmas (`RVPooled/*.lean`). -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- The row's instruction `i` executes from `before` to a state that agrees with the row's RV history (ending in
    `after`) followed by its final PC. -/
def RVPooledRowStep {p : Nat} [Fact p.Prime] (row : Row p PooledFamily) (before after : RV.State)
    (i : RV.Instr) : Prop :=
  ∃ next, RV.exec before i = some next ∧ RV.Same next { after with pc := row.finish.word.toBitVec }

/-- What the trace gives for one pooled row at RV pre-state `before` (its RV history ends in `after`), fetched from
    the program entry `entry`. Projection-free: the row's metadata is supplied separately. -/
structure RVPooledRowFacts {p : Nat} [Fact p.Prime] (trace : PooledTrace p) (initial : RV.State)
    (cells : List Cell) (row : Row p PooledFamily) (before after : RV.State) (entry : RVPooledProgramEntry) :
    Prop where
  constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
    (row.constraints trace.rom)
  active : row.assignment row.columns.execute = 1
  family : entry.data.family = row.family
  query : row.decoderQuery = entry.query
  pc : before.pc = entry.pc
  pcAligned : entry.pc.toNat % 4 = 0
  readBounds : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded
  finishBound : row.finish.word.Bounded
  history : RVHistory cells (rowEvents trace.memoryEpoch row).reverse before after
  aligned : ∀ cell ∈ cells, cell.Aligned
  rom : before.rom = initial.rom
  wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells)
  subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial)

/-- Applying a register cell's port write: the register gets the value (x0's stored value is never read). -/
theorem rv_apply_register {c : Cell} {i : BitVec 5} {v : BitVec 32} {before after : RV.State}
    (address : c.addressCode = (Cell.register i).addressCode) (apply : c.applyRV v before = some after) :
    RV.Same after (before.setReg i v) := by
  obtain rfl := cell_address_injective address
  unfold Cell.applyRV at apply
  split at apply
  · rename_i same
    obtain rfl := Option.some.inj apply
    exact RV.Same.symm (writeRV_self_same_register same (writeRV_register i v before))
  · rw [writeRV_register] at apply
    obtain rfl := Option.some.inj apply
    exact RV.Same.refl _

/-- A register cell at a port reads the register's value. -/
theorem rv_read_register {c : Cell} {i : BitVec 5} {v : BitVec 32} {before : RV.State}
    (address : c.addressCode = (Cell.register i).addressCode) (read : c.readRV before = some v) :
    before.getReg i = v := by
  obtain rfl := cell_address_injective address
  exact Option.some.inj ((readRV_register i before).symm.trans read)

/-- Agreement with `t` survives setting both PCs. -/
theorem rv_same_with_pc {after t : RV.State} (same : RV.Same after t) (pc : BitVec 32) :
    RV.Same (t.setPC pc) { after with pc := pc } :=
  ⟨rfl, fun i => (same.2.1 i).symm, same.2.2.1.symm, same.2.2.2.1.symm, same.2.2.2.2.symm⟩

/-- Applying a RAM cell's port write: the word is stored (in RAM at any address, as the native write). -/
theorem rv_apply_ram {a v : BitVec 32} {before after : RV.State}
    (apply : (Cell.ram a).applyRV v before = some after) : RV.Same after (before.store a v 4) := by
  unfold Cell.applyRV at apply
  split at apply
  · rename_i read
    obtain rfl := Option.some.inj apply
    rw [readRV_ram _ (readable_of_readRV read)] at read
    have value := Option.some.inj read
    refine ⟨rfl, fun _ => rfl, rfl, ?_, rfl⟩
    simp only [RV.State.store, ← value, rv_write_read_self]
  · rw [writeRV_ram] at apply
    obtain rfl := Option.some.inj apply
    exact RV.Same.refl _

/-- A row whose history ends in a state agreeing with `t` and whose PC advances by four is `t.nextInstr`. -/
theorem rv_state_next {before after t : RV.State} {pc : RV.Word} (same : RV.Same after t) (atPC : t.pc = before.pc)
    (next : pc = before.pc + 4) : RV.Same t.nextInstr { after with pc := pc } := by
  subst next
  rw [← atPC]
  exact rv_same_with_pc same _

/-- A row whose history writes `value` to `rd` and whose PC advances by four is `setReg` then `nextInstr`. -/
theorem rv_register_next {before after : RV.State} {rd : RV.Reg} {value pc : RV.Word}
    (same : RV.Same after (before.setReg rd value)) (next : pc = before.pc + 4) :
    RV.Same (before.setReg rd value).nextInstr { after with pc := pc } := by
  subst next
  exact rv_same_with_pc same _

/-- A three-port row with two read-only register operand ports (columns `a`, `b`) and a register destination port
    (column `c`): the operands are the pre-state registers, and the history writes the destination register. -/
theorem rv_register_row {p : Nat} [Fact p.Prime] (hp : 32 ≤ p) {cells : List Cell} {columns : TraceColumns}
    {first second destination : MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {a b c : Nat} (firstAt : first.address = .register a) (secondAt : second.address = .register b)
    (destinationAt : destination.address = .register c)
    {i j rd : BitVec 5} (hi : w a = (i.toNat : ZMod p)) (hj : w b = (j.toNat : ZMod p))
    (hd : w c = (rd.toNat : ZMod p)) {before after : RV.State}
    (history : RVHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    before.getReg i = memoryWord (first.readCode w) ∧ before.getReg j = memoryWord (second.readCode w) ∧
      RV.Same after (before.setReg rd (memoryWord (destination.writeCode w))) := by
  obtain ⟨c0, _, c1, _, c2, _, a0, r0, a1, r1, a2, _, w2⟩ :=
    rv_three_ports epoch firstReadonly secondReadonly history
  rw [firstAt, register_address_code hp hi] at a0
  rw [secondAt, register_address_code hp hj] at a1
  rw [destinationAt, register_address_code hp hd] at a2
  exact ⟨rv_read_register a0 r0, rv_read_register a1 r1, rv_apply_register a2 w2⟩

/-- A bounded read whose word is zero has the zero value code. -/
theorem rv_zero_code {p : Nat} {w : Nat → ZMod p} {port : MemoryPort}
    (bound : (readToken w port).word.Bounded) (zero : memoryWord (port.readCode w) = 0) : port.readCode w = 0 := by
  have eq := Word.eq_zero_of_bounded bound zero
  simp only [MemoryToken.word, readToken, Word.mk.injEq] at eq
  rw [← Nat.pair_unpair (port.readCode w), eq.1, eq.2]
  rfl

/-- Writing x0 changes nothing a program sees. -/
theorem rv_same_set_zero (s : RV.State) (v : RV.Word) : RV.Same (s.setReg 0 v) s := by
  refine ⟨rfl, fun j => ?_, rfl, rfl, rfl⟩
  simp only [RV.State.getReg, RV.State.setReg]
  split_ifs <;> simp_all

end Airbender.Trace.Proofs
