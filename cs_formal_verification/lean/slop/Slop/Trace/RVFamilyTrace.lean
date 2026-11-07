import Slop.Trace.RVRealizes
import Slop.Trace.RVPorts
import Slop.Trace.RVCells
import Slop.Trace.RVFetch
import Slop.Trace.RVProgram
import Slop.Trace.RVZero
import Slop.Trace.RVRom

/-! The single-family trace claims on the RV route, generic over the circuit registry `Kind` and the decoder
    projection: one composition (`rv_family_realizes`), instantiated by each family with its row step
    (`rv_family_row_steps`, from a row-local step that sees the row's program entry and RV history) and its x0 law.

    - `rv_family_row_steps`: the row's program entry is an aligned ROM word of the starting ROM image that decodes to
      `i`, the row's pre-state is at the entry's PC with the starting ROM image, so `RV.step` is `RV.exec` of `i`.
    - `rv_register_ports`: a three-port row reading two registers and writing a third, against its RV history.
    - `rv_family_realizes`: `rv_realizes` from the public RV inputs (`RVNativeInputs`). -/

namespace Airbender.Trace.Proofs
open Arithmetic

variable {Kind : Type} [CircuitLayout Kind]

/-- A row whose RV history agrees with `t` and whose PC advances by four is `t.nextInstr`. -/
theorem rv_same_next {t after : RV.State} {final : RV.Word} (same : RV.Same after t) (pc : final = t.pc + 4) :
    RV.Same t.nextInstr { after with pc := final } :=
  ⟨by simp [RV.State.nextInstr, pc], fun i => (same.2.1 i).symm, same.2.2.1.symm,
    same.2.2.2.1.symm, same.2.2.2.2.symm⟩

/-- A RAM port's update: the post-state is the pre-state with the word stored at that cell (`RV.Same`; a write of
    the word already stored changes nothing). -/
theorem rv_ram_update {address value : BitVec 32} {before after : RV.State}
    (write : (Cell.ram address).applyRV value before = some after) :
    RV.Same after (before.store address value 4) := by
  unfold Cell.applyRV at write
  split at write
  · rename_i read
    obtain rfl := Option.some.inj write
    have readable := readable_of_readRV read
    rw [readRV_ram _ readable] at read
    have stored := Option.some.inj read
    refine ⟨rfl, fun _ => rfl, rfl, ?_, rfl⟩
    simp only [RV.State.store, ← stored, rv_write_read_self]
  · rw [writeRV_ram] at write
    obtain rfl := Option.some.inj write
    exact RV.Same.refl _

/-- A row whose RV history agrees with `s` and whose final PC is `target` is `s.setPC target`. -/
theorem rv_same_setPC {s after : RV.State} (same : RV.Same after s) (target : RV.Word) :
    RV.Same (s.setPC target) { after with pc := target } :=
  ⟨rfl, fun i => (same.2.1 i).symm, same.2.2.1.symm, same.2.2.2.1.symm, same.2.2.2.2.symm⟩

/-- Setting x0 is not visible. -/
theorem rv_same_set_zero (s : RV.State) (v : RV.Word) : RV.Same (s.setReg 0 v) s := by
  refine ⟨rfl, fun j => ?_, rfl, rfl, rfl⟩
  simp only [RV.State.getReg, RV.State.setReg]
  split_ifs <;> simp_all

private theorem register_cell {cell : Cell} {index : BitVec 5} {p : Nat} {column : ZMod p}
    (code : cell.addressCode = Nat.pair 0 (Nat.pair column.val 0)) (value : column.val = index.toNat) :
    cell = .register index := by
  apply cell_address_injective
  rw [code, value]
  rfl

/-- A register port's update: the post-state is the pre-state with that register set to the written word (`RV.Same`;
    a write of the value already held changes nothing visible, x0 included). -/
theorem rv_register_update {index : BitVec 5} {value : BitVec 32} {before after : RV.State}
    (write : (Cell.register index).applyRV value before = some after) :
    RV.Same after (before.setReg index value) := by
  unfold Cell.applyRV at write
  split at write
  · rename_i same
    obtain rfl := Option.some.inj write
    exact RV.Same.symm (writeRV_self_same_register same (writeRV_register index _ before))
  · rw [writeRV_register] at write
    obtain rfl := Option.some.inj write
    exact RV.Same.refl _

/-- A three-port row reading two registers and reading/writing a third, against its RV history: the reads see the
    pre-state registers, and the post-state is the pre-state with the destination register set to the written word. -/
theorem rv_register_ports {p : Nat} {cells : List Cell} {columns : TraceColumns}
    {first second destination : MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    {a b c : Nat} (firstAt : first.address = .register a) (secondAt : second.address = .register b)
    (destinationAt : destination.address = .register c)
    {i j k : BitVec 5} (hi : (w a).val = i.toNat) (hj : (w b).val = j.toNat) (hk : (w c).val = k.toNat)
    {before after : RV.State}
    (history : RVHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    before.getReg i = memoryWord (first.readCode w) ∧ before.getReg j = memoryWord (second.readCode w) ∧
      RV.Same after (before.setReg k (memoryWord (destination.writeCode w))) := by
  obtain ⟨c0, _, c1, _, c2, _, a0, r0, a1, r1, a2, _, w2⟩ :=
    rv_three_ports epoch firstReadonly secondReadonly history
  rw [firstAt] at a0
  rw [secondAt] at a1
  rw [destinationAt] at a2
  have e0 := register_cell (column := w a) (by simpa [MemoryAddress.code] using a0) hi
  have e1 := register_cell (column := w b) (by simpa [MemoryAddress.code] using a1) hj
  have e2 := register_cell (column := w c) (by simpa [MemoryAddress.code] using a2) hk
  subst e0 e1 e2
  rw [readRV_register] at r0 r1
  exact ⟨Option.some.inj r0, Option.some.inj r1, rv_register_update w2⟩

/-- The row steps of a trace whose rows each match an entry of an RV program table: each row's step is `RV.exec` of
    its entry's instruction from the row's pre-state, which `rowStep` must show agrees with the row's RV history followed
    by its final PC. `rowStep` sees the entry's decoding, the pre-state's PC and ROM image, and the row's history. -/
theorem rv_family_row_steps {ISA : Type} {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : Data p Kind} {initial : RV.State} {cells : List Cell}
    {projection : RV.Instr → Option (DecoderData ISA)} {addresses : List (BitVec 32)}
    {program : List (RVProgramEntry ISA)} (image : rvProgramImageWith projection initial addresses = some program)
    (Fits : Row p Kind → RVProgramEntry ISA → Prop)
    (fetch : ∀ row ∈ trace.rows, ∃ entry ∈ program, Fits row entry ∧ row.decoderQuery = entry.query)
    (rowStep : ∀ row ∈ trace.rows, ∀ entry ∈ program, Fits row entry → row.decoderQuery = entry.query →
      ∀ i : RV.Instr, RV.decode entry.bits = some i → projection i = some entry.data →
      (entry.pc.toNat < RV.ROM_END ∧ entry.pc.toNat % 4 = 0) → ∀ {before after : RV.State}, before.pc = entry.pc → before.rom = initial.rom →
        RVHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
        ∃ next, RV.exec before i = some next ∧ RV.Same next { after with pc := row.finish.word.toBitVec }) :
    RVRowSteps trace initial cells := by
  intro row member before after position history
  obtain ⟨entry, present, fits, query⟩ := fetch row member
  obtain ⟨guard, bits, i, decodes, fields⟩ := rvProgram_entry_fetch image entry present
  obtain ⟨beforePC, step⟩ := rv_step_of_position position (rv_query_pc hp query) guard (bits ▸ decodes)
  have rom : before.rom = initial.rom := by
    obtain ⟨_, _, middle, _, _, writes, atState⟩ := position
    rw [atState]
    exact (rvWriteHistory_rom writes : middle.rom = initial.rom)
  obtain ⟨next, exec, same⟩ := rowStep row member entry present fits query i decodes fields guard beforePC rom history
  exact ⟨next, step.trans exec, same⟩

/-- The single-family composition: an accepted trace with public RV inputs, x0-preserving rows and one `RV.step` per
    row realizes `RV.run` from the public starting state. -/
theorem rv_family_realizes {ISA : Type} {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) {initial : RV.State} {cells : List Cell}
    {projection : RV.Instr → Option (DecoderData ISA)} {program : List (RVProgramEntry ISA)}
    (inputs : RVNativeInputs projection trace initial cells program)
    (zero : ZeroPreserving trace) (step : RVRowSteps trace initial cells) :
    RVRealizes trace initial cells := by
  have writes := RVZero.rv_zero_writes_of_preserving hp inverse accepted inputs.clocks inputs.image zero
  have start : initial.pc = trace.initial.word.toBitVec := by
    obtain ⟨timestamp, bound⟩ := inputs.initialPC
    have limbSize : limbBase < p := by dsimp [limbBase, timestampBase] at hp ⊢; omega
    have bounds := Word.ofBitVec_bound initial.pc
    change initial.pc.toNat % limbBase < limbBase ∧ initial.pc.toNat / limbBase < limbBase at bounds
    have encoded : (initialStateRV (p := p) initial timestamp).word = Word.ofBitVec initial.pc := by
      change Word.mk ((initial.pc.toNat % limbBase : Nat) : ZMod p).val
        ((initial.pc.toNat / limbBase : Nat) : ZMod p).val = Word.ofBitVec initial.pc
      rw [ZMod.val_natCast_of_lt (lt_trans bounds.1 limbSize),
        ZMod.val_natCast_of_lt (lt_trans bounds.2 limbSize)]
      rfl
    rw [← bound, encoded, Word.ofBitVec_roundtrip]
  exact rv_realizes hp inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned writes start step

end Airbender.Trace.Proofs
