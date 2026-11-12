module
public import Proven.UnifiedReduced.RV.Step
public import Proven.UnifiedReduced.RV.JumpArithmetic
public import Proven.JumpBranchSlt.RVData
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

/-! JAL/JALR rows on the RV route: the unified jump arithmetic (`jump_link`, `jump_pc`) against `RV.exec`. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- A jump's step agrees with the history: the link value is written unless `rd` is x0. -/
theorem jump_same {s after : RV.State} {rd : RV.Reg} {written link target : RV.Word}
    (same : RV.Same after (s.setReg rd written)) (value : rd ≠ 0 → written = link) :
    RV.Same ((s.setPC target).setReg rd link) { after with pc := target } := by
  refine ⟨rfl, fun k => ?_, same.2.2.1.symm, same.2.2.2.1.symm, same.2.2.2.2.symm⟩
  have h := same.2.1 k
  change ((s.setPC target).setReg rd link).getReg k = after.getReg k
  rw [h]
  simp only [RV.r_set, RV.jump_r]
  split_ifs with zero equal
  · rfl
  · subst equal
    exact (value zero).symm
  · rfl

/-- Flags and register updates of a jump row with unified mask `1024 * jumpMask`. -/
private theorem jump_context {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {i : RV.Instr} (facts : RowFacts words cells epoch w s after entry i) {rd : RV.Reg} (indirect : Bool)
    (mask : entry.data.mask = 1024 * ((if indirect then 2 else 1) + if rd = 0 then 16 else 0))
    (destination : entry.data.rd = rd) :
    (w 21 = (if indirect then 0 else 1) ∧ w 22 = (if indirect then 1 else 0)) ∧ (w 23 = 0 ∧ w 24 = 0) ∧
      (w 26 = 0 ∧ w 27 = 0) ∧ w 28 = 0 ∧ w 81 = 0 ∧ w 25 = (if rd = 0 then 1 else 0) ∧
      RV.Same after (s.setReg rd (Word.mk (w 50).val (w 51).val).toBitVec) := by
  have flags := facts.flags (by omega)
  rw [mask] at flags
  have bit (k : Fin 19) (b : Bool)
      (eq : (1024 * ((if indirect then 2 else 1) + if rd = 0 then 16 else 0)).testBit k.val = b) :
      w (11 + k.val) = if b then 1 else 0 := by rw [flags k, eq]
  have facts' : (w 21 = (if indirect then 0 else 1) ∧ w 22 = (if indirect then 1 else 0)) ∧ (w 23 = 0 ∧ w 24 = 0) ∧
      (w 26 = 0 ∧ w 27 = 0) ∧ w 28 = 0 ∧ w 29 = 0 ∧ w 25 = (if rd = 0 then 1 else 0) := by
    cases indirect <;> by_cases zero : rd = 0 <;> simp only [zero, ↓reduceIte, Bool.false_eq_true] at bit ⊢
    all_goals exact ⟨⟨by first | simpa using bit 10 true (by decide) | simpa using bit 10 false (by decide),
        by first | simpa using bit 11 true (by decide) | simpa using bit 11 false (by decide)⟩,
      ⟨by simpa using bit 12 false (by decide), by simpa using bit 13 false (by decide)⟩,
      ⟨by simpa using bit 15 false (by decide), by simpa using bit 16 false (by decide)⟩,
      by simpa using bit 17 false (by decide), by simpa using bit 18 false (by decide),
      by first | simpa using bit 14 true (by decide) | simpa using bit 14 false (by decide)⟩
  obtain ⟨selected, other, binary, load, store, marker⟩ := facts'
  have gate := Verification.assertion_of_holds facts.core ⟨39, by rw [constraint_count]; decide⟩
  op_index at gate
  have noROM : w 81 = 0 := by
    simpa [Expression.eval, Verification.environment, load] using gate
  have indices := facts.indices (by dsimp [limbBase]; omega)
  rw [destination] at indices
  have write := rv_register_write facts.core store indices.2.2 epoch facts.history
  exact ⟨selected, other, binary, load, noROM, marker, write.2⟩

private theorem link_value {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} {rd : RV.Reg} {pc : RV.Word}
    (marker : w 25 = if rd = 0 then 1 else 0)
    (link : (Word.mk (w 50).val (w 51).val).toBitVec = if w 25 = 1 then 0 else pc + 4) :
    rd ≠ 0 → (Word.mk (w 50).val (w 51).val).toBitVec = pc + 4 := by
  intro nonzero
  rw [link, marker]
  by_cases z : rd = 0
  · exact absurd z nonzero
  · simp only [z, ↓reduceIte, zero_ne_one]

theorem jal_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {rd : RV.Reg} {offset : RV.Word}
    (facts : RowFacts words cells epoch w s after entry (.jal rd offset))
    (data : entry.data = jumpFields ⟨(), 0, 0, rd, Word.ofBitVec offset, if rd = 0 then 17 else 1, 0⟩) :
    RowStep w s after (.jal rd offset) := by
  have mask : entry.data.mask = 1024 * ((if false then 2 else 1) + if rd = 0 then 16 else 0) := by
    rw [data]; change 1024 * (if rd = 0 then 17 else 1) = _; split <;> simp_all
  obtain ⟨selected, other, binary, _, noROM, marker, write⟩ :=
    jump_context hp facts false mask (by rw [data]; rfl)
  simp only [Bool.false_eq_true, ↓reduceIte] at selected
  have pcWord := facts.pcWord (by dsimp [limbBase]; omega)
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := pcWord ▸ Word.ofBitVec_bound _
  have link := jump_link (by omega) facts.core (by rw [selected.1, selected.2]; simp) other pcBound
  rw [pcWord, Word.ofBitVec_roundtrip] at link
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at immediate
  simp only [jumpFields, DecoderData.mapFamily] at immediate
  have even := JumpBranchSlt.Proofs.decode_jal_even facts.decodes
  have aligned := facts.pcAligned
  rw [← facts.pc] at aligned
  have target := jump_pc hp false facts.core (base := Word.mk (w 0).val (w 1).val) (offset := Word.ofBitVec offset)
    (final := Word.mk (w 30).val (w 31).val) (by simpa using selected) other binary noROM
    ⟨rfl, rfl, by rw [← immediate]; exact (ZMod.natCast_zmod_val _).symm,
      by rw [← immediate]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
    pcBound.1 (fun h => absurd h (by decide)) (Word.ofBitVec_bound _)
    (fun _ => ⟨by rw [pcWord]; dsimp [Word.ofBitVec, limbBase]; omega,
      by dsimp [Word.ofBitVec, limbBase]; omega⟩) (pc_bounds facts.core).2
  simp only [Bool.false_eq_true, ↓reduceIte] at target
  rw [pcWord, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip] at target
  refine ⟨_, RV.exec_jal s rd offset (target.1 ▸ target.2), ?_⟩
  rw [← target.1]
  exact jump_same write (link_value marker link)

theorem jalr_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {rd rs1 : RV.Reg} {offset : RV.Word}
    (facts : RowFacts words cells epoch w s after entry (.jalr rd rs1 offset))
    (data : entry.data = jumpFields ⟨(), rs1, 0, rd, Word.ofBitVec offset, if rd = 0 then 18 else 2, 0⟩) :
    RowStep w s after (.jalr rd rs1 offset) := by
  have mask : entry.data.mask = 1024 * ((if true then 2 else 1) + if rd = 0 then 16 else 0) := by
    rw [data]; change 1024 * (if rd = 0 then 18 else 2) = _; split <;> simp_all
  obtain ⟨selected, other, binary, load, noROM, marker, write⟩ :=
    jump_context hp facts true mask (by rw [data]; rfl)
  simp only [↓reduceIte] at selected
  have pcWord := facts.pcWord (by dsimp [limbBase]; omega)
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := pcWord ▸ Word.ofBitVec_bound _
  have link := jump_link (by omega) facts.core (by rw [selected.1, selected.2]; simp) other pcBound
  rw [pcWord, Word.ofBitVec_roundtrip] at link
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at immediate
  simp only [jumpFields, DecoderData.mapFamily] at immediate
  have reads := rv_register_reads (by dsimp [limbBase]; omega) facts.core load facts.query epoch facts.history
  rw [data] at reads
  have target := jump_pc hp true facts.core (base := Word.mk (w 36).val (w 37).val)
    (offset := Word.ofBitVec offset) (final := Word.mk (w 30).val (w 31).val) (by simpa using selected) other
    binary noROM
    ⟨rfl, rfl, by rw [← immediate]; exact (ZMod.natCast_zmod_val _).symm,
      by rw [← immediate]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
    facts.leftBound.1 (fun _ => facts.leftBound.2) (Word.ofBitVec_bound _)
    (fun h => absurd h (by decide)) (pc_bounds facts.core).2
  simp only [↓reduceIte] at target
  have source : s.getReg rs1 = (Word.mk (w 36).val (w 37).val).toBitVec := reads.1
  rw [Word.ofBitVec_roundtrip, ← source, show (0xfffffffe : BitVec 32) = ~~~(1 : RV.Word) by decide] at target
  refine ⟨_, RV.exec_jalr s rd rs1 offset (target.1 ▸ target.2), ?_⟩
  rw [← target.1]
  exact jump_same write (link_value marker link)

end Airbender.UnifiedReduced.Proofs.RV
