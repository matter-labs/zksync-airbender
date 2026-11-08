module
public import Slop.UnifiedReduced.RV.Row
public import Slop.ISA.RV.Step
public import Human.Circuits.UnifiedReduced.Tables.SetupRV

@[expose] public section

/-! The per-row obligation of the unified RV route (`RowStep`: `RV.exec` of the row's decoded instruction agrees with
    the row's RV history followed by its final PC) and the facts every row gives (`RowFacts`). Proved here for the NOP
    rows (x0 preprocessing), ADD/SUB/ADDI/LUI/AUIPC and TRIADD. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- What the trace gives for one unified row at RV pre-state `s` (its RV history ends in `after`), fetched from the
    RV program entry `entry`, whose bytes decode to `i`. -/
structure RowFacts {p : Nat} [Fact p.Prime] (words : Nat → BitVec 32) (cells : List Cell) (epoch : Nat)
    (w : Nat → ZMod p) (s after : RV.State) (entry : RVProgramEntry) (i : RV.Instr) : Prop where
  core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.tableWith words))
  active : w 4 = 1
  query : decoderQuery w = entry.query
  fields : rvDecoderFields i = some entry.data
  decodes : RV.decode entry.bits = some i
  pc : s.pc = entry.pc
  pcAligned : entry.pc.toNat % 4 = 0
  leftBound : (Word.mk (w 36).val (w 37).val).Bounded
  rightBound : (Word.mk (w 42).val (w 43).val).Bounded
  oldBound : (Word.mk (w 48).val (w 49).val).Bounded
  history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse s after
  cellsAligned : ∀ cell ∈ cells, cell.Aligned
  /-- The setup table's ROM words are the pre-state's ROM image. -/
  romImage : words = ROM.wordsRV s

/-- The row's instruction executes to a state that agrees with its history and final PC. -/
def RowStep {p : Nat} (w : Nat → ZMod p) (s after : RV.State) (i : RV.Instr) : Prop :=
  ∃ next, RV.exec s i = some next ∧ RV.Same next { after with pc := (Word.mk (w 30).val (w 31).val).toBitVec }

theorem mask_column {p : Nat} {w : Nat → ZMod p} {mask : Nat}
    (flags : ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] = if mask.testBit i.val then 1 else 0)
    (k : Fin 19) : w (11 + k.val) = if mask.testBit k.val then 1 else 0 := by
  have flag := flags k
  fin_cases k <;> simpa [importedConstraintsDecoderColumns] using flag

theorem RowFacts.flags {p : Nat} [Fact p.Prime] (hp : 524288 < p) {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) :
    ∀ k : Fin 19, w (11 + k.val) = if entry.data.mask.testBit k.val then 1 else 0 :=
  mask_column (rv_decoder_selectors hp facts.core (rv_field_bounds facts.fields).2.1 facts.query)

theorem RowFacts.pcWord {p : Nat} [Fact p.Prime] (hp : limbBase < p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {i : RV.Instr} (facts : RowFacts words cells epoch w s after entry i) :
    Word.mk (w 0).val (w 1).val = Word.ofBitVec s.pc := by
  rw [facts.pc]
  exact rv_native_query_pc_word hp facts.query

theorem RowFacts.immediate {p : Nat} [Fact p.Prime] (hp : limbBase < p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {i : RV.Instr} (facts : RowFacts words cells epoch w s after entry i) :
    Word.mk (w 8).val (w 9).val = entry.data.immediate :=
  rv_native_query_immediate_word hp (rv_field_bounds facts.fields).1 facts.query

theorem RowFacts.indices {p : Nat} [Fact p.Prime] (hp : limbBase < p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {i : RV.Instr} (facts : RowFacts words cells epoch w s after entry i) :
    (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧ (w 7).val = entry.data.rd.toNat :=
  rv_native_query_indices hp facts.query

/-- Rows outside the jump/branch/comparison selectors advance the PC by four. -/
theorem RowFacts.nextPC {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {i : RV.Instr} (facts : RowFacts words cells epoch w s after entry i)
    (outside : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0) :
    (Word.mk (w 30).val (w 31).val).toBitVec = s.pc + 4 := by
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[0]) facts.query
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[1]) facts.query
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  have result := pc_successor (by omega) facts.core facts.active outside
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 30).val (w 31).val)
    ⟨low, high, rfl, rfl⟩ (Word.ofBitVec_bound _)
  rw [result.2.2, Word.ofBitVec_roundtrip, facts.pc]

/-! ### x0 preprocessing -/

theorem same_set_zero (s : RV.State) (v : RV.Word) : RV.Same (s.setReg 0 v) s := by
  refine ⟨rfl, fun j => ?_, rfl, rfl, rfl⟩
  simp only [RV.State.getReg, RV.State.setReg]
  split_ifs <;> simp_all

/-- An instruction the reduced machine turns into `Nop` only advances the PC (up to x0's stored value). -/
theorem nop_exec (s : RV.State) {i : RV.Instr} (nop : rvNopWrite i = true) :
    ∃ next, RV.exec s i = some next ∧ RV.Same next s.nextInstr := by
  cases i with
  | load n sg rd rs1 off =>
    have shape : rd = 0 := by
      unfold rvNopWrite at nop
      split at nop <;> simp_all
    subst shape
    exact ⟨_, RV.exec_load_x0 s n sg rs1 off, RV.Same.refl _⟩
  | op op rd rs1 rs2 =>
    have zero : rd = 0 := by cases op <;> simp_all [rvNopWrite]
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | opImm op rd rs1 imm =>
    have zero : rd = 0 := by simpa [rvNopWrite] using nop
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | lui rd imm =>
    have zero : rd = 0 := by simpa [rvNopWrite] using nop
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | auipc rd imm =>
    have zero : rd = 0 := by simpa [rvNopWrite] using nop
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | rev8 rd rs1 =>
    have zero : rd = 0 := by simpa [rvNopWrite] using nop
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | mop op rd rs1 rs2 =>
    have zero : rd = 0 := by simpa [rvNopWrite] using nop
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | xorRot n rd rs1 =>
    have zero : rd = 0 := by simpa [rvNopWrite] using nop
    subst zero
    exact ⟨_, rfl, (same_set_zero s _).nextInstr⟩
  | _ => simp [rvNopWrite] at nop

/-- A NOP row (ADD x0, x0, x0) retires the reduced machine's `Nop`. -/
theorem nop_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) (nop : rvNopWrite i = true)
    (data : entry.data = rvNopFields) : RowStep w s after i := by
  have flags := facts.flags (by omega)
  rw [data] at flags
  have f (k : Fin 19) (small : k.val ≠ 0) : w (11 + k.val) = 0 := by
    rw [flags k, show (rvNopFields.mask).testBit k.val = false from
      Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow small)]
    rfl
  have indices := facts.indices (by dsimp [limbBase]; omega)
  rw [data] at indices
  have write := rv_register_write facts.core (f 18 (by decide)) indices.2.2 epoch facts.history
  have pc := facts.nextPC hp ⟨f 10 (by decide), f 11 (by decide), f 12 (by decide), f 13 (by decide)⟩
  obtain ⟨next, exec, same⟩ := nop_exec s nop
  refine ⟨next, exec, same.trans ?_⟩
  exact (same_set_zero s _).nextInstr.symm.trans (rv_register_next write.2 pc)

/-! ### ADD/SUB/ADDI/LUI/AUIPC and TRIADD -/

theorem limbs_cast {p : Nat} [Fact p.Prime] (x : ZMod p) : ((x.val : Nat) : ZMod p) = x := ZMod.natCast_zmod_val x

theorem add_limbs {p : Nat} [Fact p.Prime] (hp : 196608 < p) {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 11 = 1) (others : w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0)
    (left : (Word.mk (w 36).val (w 37).val).Bounded) (right : (Word.mk (w 42).val (w 43).val).Bounded)
    (immediate : (Word.mk (w 8).val (w 9).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec = (Word.mk (w 36).val (w 37).val).toBitVec +
      (Word.mk (w 42).val (w 43).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec := by
  obtain ⟨s12, s13, s14, s15, s16, s17, s20⟩ := others
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, s12, s13, s14, s15, s16, s17, s20] at lo hi
  have carry := boolean_val (local_flags h 21)
  have wrap := boolean_val (local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at wrap
  exact Word.add_of_limbs (carry := (w 53).val) (wrap := (w 52).val)
    (output := Word.mk (w 50).val (w 51).val) hp left right immediate
    (destination_bounds h) (le_trans carry (by decide)) (le_trans wrap (by decide))
    (by simp only [limbs_cast]; linear_combination lo) (by simp only [limbs_cast]; linear_combination hi)

theorem sub_limbs {p : Nat} [Fact p.Prime] (hp : 196608 < p) {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 12 = 1) (others : w 11 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0)
    (left : (Word.mk (w 36).val (w 37).val).Bounded) (right : (Word.mk (w 42).val (w 43).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec = (Word.mk (w 36).val (w 37).val).toBitVec -
      (Word.mk (w 42).val (w 43).val).toBitVec := by
  obtain ⟨s11, s13, s14, s15, s16, s17, s20⟩ := others
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, s11, s13, s14, s15, s16, s17, s20] at lo hi
  have carry := boolean_val (local_flags h 21)
  have wrap := boolean_val (local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at wrap
  exact Word.sub_of_limbs (p := p) (borrow := (w 53).val) (wrap := (w 52).val)
    (output := Word.mk (w 50).val (w 51).val) (show 131072 < p by omega) left right
    (destination_bounds h) carry wrap
    (by simp only [limbs_cast]; linear_combination lo) (by simp only [limbs_cast]; linear_combination hi)

theorem auipc_limbs {p : Nat} [Fact p.Prime] (hp : 196608 < p) {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 13 = 1) (others : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0)
    (pc : (Word.mk (w 0).val (w 1).val).Bounded) (immediate : (Word.mk (w 8).val (w 9).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec = (Word.mk (w 0).val (w 1).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec := by
  obtain ⟨s11, s12, s14, s15, s16, s17, s20⟩ := others
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, s11, s12, s14, s15, s16, s17, s20] at lo hi
  have carry := boolean_val (local_flags h 21)
  have wrap := boolean_val (local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at wrap
  have result := Word.add_of_limbs (carry := (w 53).val) (wrap := (w 52).val) (right := ⟨0, 0⟩)
    (output := Word.mk (w 50).val (w 51).val) hp pc
    ⟨by decide, by decide⟩ immediate (destination_bounds h) (le_trans carry (by decide)) (le_trans wrap (by decide))
    (by simp only [limbs_cast, Nat.cast_zero, add_zero]; linear_combination lo)
    (by simp only [limbs_cast, Nat.cast_zero, add_zero]; linear_combination hi)
  simpa [Word.toBitVec, Word.value] using result

theorem triadd_limbs {p : Nat} [Fact p.Prime] (hp : 196608 < p) {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 20 = 1) (others : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0)
    (left : (Word.mk (w 36).val (w 37).val).Bounded) (right : (Word.mk (w 42).val (w 43).val).Bounded)
    (old : (Word.mk (w 48).val (w 49).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec = (Word.mk (w 36).val (w 37).val).toBitVec +
      (Word.mk (w 42).val (w 43).val).toBitVec + (Word.mk (w 48).val (w 49).val).toBitVec := by
  obtain ⟨s11, s12, s13, s14, s15, s16, s17⟩ := others
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, s11, s12, s13, s14, s15, s16, s17] at lo hi
  have c1 := boolean_val (local_flags h 21)
  have c2 := boolean_val (local_flags h 22)
  have w1 := boolean_val (local_flags h 20)
  have w2 := boolean_val (local_flags h 23)
  change (w 53).val ≤ 1 at c1
  change (w 54).val ≤ 1 at c2
  change (w 52).val ≤ 1 at w1
  change (w 55).val ≤ 1 at w2
  exact Word.add_of_limbs (carry := (w 53).val + (w 54).val) (wrap := (w 52).val + (w 55).val)
    (output := Word.mk (w 50).val (w 51).val) hp left right old
    (destination_bounds h) (by omega) (by omega)
    (by push_cast; simp only [limbs_cast]; linear_combination lo)
    (by push_cast; simp only [limbs_cast]; linear_combination hi)

end Airbender.UnifiedReduced.Proofs.RV
