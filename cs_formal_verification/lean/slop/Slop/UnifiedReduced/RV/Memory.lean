import Slop.UnifiedReduced.RV.Step
import Slop.UnifiedReduced.RV.ROMValue

/-! LW/SW rows (decoder bits 17/18) on the RV route. A LW below `ROM_END` reads the ROM image through the setup
    table's ROM region (`word_rom_value`); from `ROM_END` on it copies the second port's RAM read. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- The first port reads the pre-state register `rs1`, whatever the second port addresses. -/
theorem rv_source_read {p : Nat} [Fact p.Prime] (hp : limbBase < p) {w : Nat → ZMod p} {entry : RVProgramEntry}
    (query : decoderQuery w = entry.query) {cells : List Cell} (epoch : Nat) {before after : RV.State}
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    before.getReg entry.data.rs1 = (Word.mk (w 36).val (w 37).val).toBitVec := by
  have indices := rv_native_query_indices hp query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧ (w 7).val = entry.data.rd.toNat
    at indices
  obtain ⟨c0, _, _, _, _, _, a0, r0, _⟩ := rv_row_ports epoch history
  have e0 : c0 = .register entry.data.rs1 := by
    apply cell_address_injective
    rw [a0, indices.1]
    rfl
  subst e0
  rw [readRV_register] at r0
  exact Option.some.inj r0

theorem rv_next_of_same {t after : RV.State} {final : RV.Word} (same : RV.Same after t) (pc : final = t.pc + 4) :
    RV.Same t.nextInstr { after with pc := final } :=
  ⟨by simp [RV.State.nextInstr, pc], fun i => (same.2.1 i).symm, same.2.2.1.symm, same.2.2.2.1.symm,
    same.2.2.2.2.symm⟩

theorem lw_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {rd rs1 : RV.Reg} {offset : RV.Word}
    (facts : RowFacts words cells epoch w s after entry (.load 4 true rd rs1 offset)) (nonzero : rd ≠ 0)
    (data : entry.data = ⟨.machine, rs1, 0, rd, Word.ofBitVec offset, 131072, 0⟩) :
    RowStep w s after (.load 4 true rd rs1 offset) := by
  have flags := facts.flags (by omega)
  rw [data] at flags
  have bit (k : Fin 19) (b : Bool) (eq : (131072 : Nat).testBit k.val = b) :
      w (11 + k.val) = if b then 1 else 0 := by rw [flags k, eq]
  have load : w 28 = 1 := by simpa using bit 17 true (by decide)
  have store : w 29 = 0 := by simpa using bit 18 false (by decide)
  have other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 :=
    ⟨by simpa using bit 10 false (by decide), by simpa using bit 11 false (by decide),
      by simpa using bit 12 false (by decide), by simpa using bit 13 false (by decide)⟩
  have indices := facts.indices (by dsimp [limbBase]; omega)
  rw [data] at indices
  have source := rv_source_read (by dsimp [limbBase]; omega) facts.query epoch facts.history
  rw [data] at source
  have read := rv_load_read load facts.cellsAligned epoch facts.history
  have write := rv_register_write facts.core store indices.2.2 epoch facts.history
  have pc := facts.nextPC hp other
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at immediate
  have address := word_memory_address (by omega) false facts.core (by simpa using load) (by simpa using store)
    facts.leftBound (immediate ▸ Word.ofBitVec_bound _) (by simpa using read.1)
  simp only [Bool.false_eq_true, ↓reduceIte] at address
  rw [immediate, Word.ofBitVec_roundtrip, ← source] at address
  have bound := read.1
  have value := Word.toBitVec_toNat bound
  change (Word.mk (w 38).val (w 39).val).toBitVec.toNat = (w 38).val + 65536 * (w 39).val at value
  have loaded : RV.read s.loadView (Word.mk (w 38).val (w 39).val).toBitVec 4 =
      (Word.mk (w 50).val (w 51).val).toBitVec := by
    rcases local_flags facts.core 22 with ram | rom
    · change w 54 = 0 at ram
      have copy := word_memory_copy false facts.core (by simpa using load) (by simpa using store) ram
      change w 50 = w 42 ∧ w 51 = w 43 at copy
      have classify := (word_rom_selection (by omega) false facts.core (by simpa using load) (by simpa using store)).1
      change w 54 = (if (w 39).val < 64 then 1 else 0) at classify
      have high : 64 ≤ (w 39).val := by
        by_contra low
        simp only [show (w 39).val < 64 from by omega, ↓reduceIte, ram] at classify
        exact zero_ne_one classify
      rw [RV.read_loadView_ram s _ 4 (by unfold RV.ROM_END; omega) (by have := read.2.2.1; unfold RV.readable RV.RAM_END at this; omega),
        read.2.2.2, copy.1, copy.2]
    · change w 54 = 1 at rom
      obtain ⟨inside, aligned, word⟩ := word_rom_value hp facts.core facts.active load rom
      have small := bound.1
      dsimp [limbBase] at small
      rw [word, facts.romImage, RV.read_loadView_rom s _ 4 (by unfold RV.ROM_END; omega)]
      simp only [ROM.wordsRV, show 4 * (((w 38).val + 65536 * (w 39).val) / 4) + 4 ≤ RV.RAM_END from by
        unfold RV.RAM_END; omega, ↓reduceIte]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [value, BitVec.toNat_ofNat]
      omega
  rw [address] at read loaded
  refine ⟨_, RV.exec_load s 4 true rd rs1 offset nonzero read.2.1 read.2.2.1, ?_⟩
  simp only [↓reduceIte, RV.sext_word, loaded]
  exact rv_register_next write.2 pc

theorem sw_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {rs2 rs1 : RV.Reg} {offset : RV.Word}
    (facts : RowFacts words cells epoch w s after entry (.store 4 rs2 rs1 offset))
    (data : entry.data = ⟨.machine, rs1, rs2, 0, Word.ofBitVec offset, 262144, 0⟩) :
    RowStep w s after (.store 4 rs2 rs1 offset) := by
  have flags := facts.flags (by omega)
  rw [data] at flags
  have bit (k : Fin 19) (b : Bool) (eq : (262144 : Nat).testBit k.val = b) :
      w (11 + k.val) = if b then 1 else 0 := by rw [flags k, eq]
  have load : w 28 = 0 := by simpa using bit 17 false (by decide)
  have store : w 29 = 1 := by simpa using bit 18 true (by decide)
  have other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 :=
    ⟨by simpa using bit 10 false (by decide), by simpa using bit 11 false (by decide),
      by simpa using bit 12 false (by decide), by simpa using bit 13 false (by decide)⟩
  have reads := rv_register_reads (by dsimp [limbBase]; omega) facts.core load facts.query epoch facts.history
  rw [data] at reads
  have written := rv_store_write (by omega) facts.core load store facts.cellsAligned epoch facts.history
  have pc := facts.nextPC hp other
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at immediate
  have address := word_memory_address (by omega) true facts.core (by simpa using load) (by simpa using store)
    facts.leftBound (immediate ▸ Word.ofBitVec_bound _) (by simpa using written.1)
  simp only [↓reduceIte] at address
  rw [immediate, Word.ofBitVec_roundtrip, ← reads.1] at address
  obtain ⟨_, aligned, writable, same⟩ := written
  rw [address] at aligned writable same
  refine ⟨_, RV.exec_store s 4 rs2 rs1 offset aligned writable, ?_⟩
  have readonly := Verification.assertion_of_holds facts.core ⟨38, by rw [constraint_count]; decide⟩
  have ram : w 54 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      store] using readonly
  have copy := word_memory_copy true facts.core (by simpa using load) (by simpa using store) ram
  change w 50 = w 42 ∧ w 51 = w 43 at copy
  rw [reads.2]
  rw [copy.1, copy.2] at same
  exact rv_next_of_same same pc

end Airbender.UnifiedReduced.Proofs.RV
