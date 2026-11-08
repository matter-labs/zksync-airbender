module
public import Slop.UnifiedReduced.RV.Step
public import Slop.UnifiedReduced.RV.ControlMembership
public import Slop.UnifiedReduced.RV.JumpArithmetic
public import Slop.UnifiedReduced.ControlContext
public import Slop.JumpBranchSlt.RVRow

@[expose] public section

/-! Jump/branch/comparison rows (decoder bits 10–14) on the RV route. Comparisons and branches project onto the
    JumpBranchSlt circuit (`control_constraints`) and reuse its RV row lemmas (`rv_comparison_exec`,
    `rv_branch_exec`); jumps use the unified jump arithmetic (`jump_link`, `jump_pc`). -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- A comparison or branch row seen as a JumpBranchSlt row (`controlAssignment`), and its destination update. -/
theorem control_row_facts {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {i : RV.Instr} (facts : RowFacts words cells epoch w s after entry i) {j : DecoderData Unit}
    (data : entry.data = jumpFields j) (jbs : JumpBranchSlt.rvDecoderFields i = some j)
    (shape : j.mask = 4 ∨ j.mask = 24) (form : j.mask = 4 → j.rs2 = 0 ∨ j.immediate = ⟨0, 0⟩) :
    JumpBranchSlt.Proofs.RVRowFacts (controlAssignment w) s j ∧
      RV.Same after (s.setReg j.rd (Word.mk (w 50).val (w 51).val).toBitVec) := by
  have mask : entry.data.mask = 1024 * j.mask := by rw [data]; rfl
  have flags := facts.flags (by omega)
  rw [mask] at flags
  have bit (k : Fin 19) (b : Bool) (eq : (1024 * j.mask).testBit k.val = b) :
      w (11 + k.val) = if b then 1 else 0 := by rw [flags k, eq]
  have zeros : w 21 = 0 ∧ w 22 = 0 ∧ w 26 = 0 ∧ w 27 = 0 ∧ w 28 = 0 ∧ w 29 = 0 := by
    rcases shape with m | m
    all_goals rw [m] at bit
    all_goals exact ⟨by simpa using bit 10 false (by decide), by simpa using bit 11 false (by decide),
      by simpa using bit 15 false (by decide), by simpa using bit 16 false (by decide),
      by simpa using bit 17 false (by decide), by simpa using bit 18 false (by decide)⟩
  obtain ⟨s21, s22, s26, s27, s28, s29⟩ := zeros
  have selectors : w 23 + w 24 = 1 ∧ w 24 * (1 - w 25) = 0 ∧ (j.mask = 4 → w 23 = 1) := by
    rcases shape with m | m
    · rw [m] at bit
      have s23 : w 23 = 1 := by simpa using bit 12 true (by decide)
      have s24 : w 24 = 0 := by simpa using bit 13 false (by decide)
      exact ⟨by simp [s23, s24], by simp [s24], fun _ => s23⟩
    · rw [m] at bit
      have s23 : w 23 = 0 := by simpa using bit 12 false (by decide)
      have s24 : w 24 = 1 := by simpa using bit 13 true (by decide)
      have s25 : w 25 = 1 := by simpa using bit 14 true (by decide)
      exact ⟨by simp [s23, s24], by simp [s24, s25], fun h => absurd (m.symm.trans h) (by decide)⟩
  have gate := Verification.assertion_of_holds facts.core ⟨39, by rw [constraint_count]; decide⟩
  have noROM : w 81 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, s28] using gate
  have indices := facts.indices (by dsimp [limbBase]; omega)
  rw [data] at indices
  have reads := rv_register_reads (by dsimp [limbBase]; omega) facts.core s28 facts.query epoch facts.history
  rw [data] at reads
  simp only [jumpFields, DecoderData.mapFamily] at reads indices
  have write := rv_register_write facts.core s29 indices.2.2 epoch facts.history
  have funct3 : w 10 = (j.funct3 : ZMod p) := by
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) facts.query
    change w 10 = (entry.data.funct3 : ZMod p) at tag
    rw [data] at tag
    exact tag
  have bounds := JumpBranchSlt.Proofs.rv_decoder_field_bounds jbs
  have smallTag : (w 10).val < 8 := by
    rw [funct3, ZMod.val_natCast_of_lt (by omega)]
    exact bounds.2.2
  have immediate : w 8 = (j.immediate.lo : ZMod p) ∧ w 9 = (j.immediate.hi : ZMod p) := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) facts.query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) facts.query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    rw [data] at low high
    exact ⟨low, high⟩
  have total : w 21 + w 22 + w 23 + w 24 = 1 := by rw [s21, s22]; simpa using selectors.1
  have signSource := Control.Proofs.right_sign_source facts.core total
  have rightHi : (w 60).val < 65536 := by
    rw [signSource]
    by_cases c : w 23 = 0
    · rw [c, zero_mul, add_zero]
      exact facts.rightBound.2
    have one : w 23 = 1 := by
      rcases local_flags facts.core 13 with z | o
      · exact absurd z c
      · exact o
    have comparison : j.mask = 4 := by
      rcases shape with m | m
      · exact m
      · rw [m] at bit
        have s23 : w 23 = 0 := by simpa using bit 12 false (by decide)
        exact absurd s23 c
    rw [one, one_mul]
    rcases form comparison with zero | zero
    · rw [zero] at reads
      have limbs := Word.eq_zero_of_bounded facts.rightBound (by rw [← reads.2]; rfl)
      have z43 : w 43 = 0 := by simpa using congrArg Word.hi limbs
      rw [z43, zero_add, immediate.2, ZMod.val_natCast_of_lt (lt_of_lt_of_le bounds.1.2 (by dsimp [limbBase]; omega))]
      exact bounds.1.2
    · have z9 : w 9 = 0 := by rw [immediate.2, zero]; simp
      rw [z9, add_zero]
      exact facts.rightBound.2
  have constraints := control_constraints hp facts.core ⟨s21, s22⟩ selectors.1 selectors.2.1 ⟨s26, s27⟩ noROM
    facts.leftBound.2 rightHi smallTag
  have pcWord := facts.pcWord (by dsimp [limbBase]; omega)
  refine ⟨{
    constraints := constraints
    pcWord := pcWord
    pcAligned := facts.pc ▸ facts.pcAligned
    immediateLo := immediate.1
    immediateHi := immediate.2
    funct3 := funct3
    flags := ?_
    left := reads.1
    right := reads.2
    leftBound := facts.leftBound
    rightBound := facts.rightBound
    finalHi := (pc_bounds facts.core).2 }, write.2⟩
  intro k
  have value := bit ⟨10 + k.val, by omega⟩ (j.mask.testBit k.val) (by
    change (1024 * j.mask).testBit (10 + k.val) = j.mask.testBit k.val
    rw [show 1024 * j.mask = 2 ^ 10 * j.mask by norm_num, Nat.testBit_two_pow_mul]
    simp)
  fin_cases k <;> simpa [controlAssignment] using value

/-- SLT/SLTU/SLTI/SLTIU rows. -/
theorem comparison_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    (input : JumpBranchSlt.Comparison.RVInput) (before : input.before = s)
    (facts : RowFacts words cells epoch w s after entry (JumpBranchSlt.Comparison.rvInstruction input))
    (data : entry.data = jumpFields (JumpBranchSlt.Proofs.comparisonData input))
    (jbs : JumpBranchSlt.rvDecoderFields (JumpBranchSlt.Comparison.rvInstruction input) =
      some (JumpBranchSlt.Proofs.comparisonData input)) :
    RowStep w s after (JumpBranchSlt.Comparison.rvInstruction input) := by
  have form : (JumpBranchSlt.Proofs.comparisonData input).rs2 = 0 ∨
      (JumpBranchSlt.Proofs.comparisonData input).immediate = ⟨0, 0⟩ := by
    unfold JumpBranchSlt.Proofs.comparisonData
    split <;> simp
  have mask : (JumpBranchSlt.Proofs.comparisonData input).mask = 4 := by
    unfold JumpBranchSlt.Proofs.comparisonData; split <;> rfl
  have rd : (JumpBranchSlt.Proofs.comparisonData input).rd = input.rd := by
    unfold JumpBranchSlt.Proofs.comparisonData; split <;> rfl
  obtain ⟨rowFacts, write⟩ := control_row_facts hp facts data jbs (Or.inl mask) (fun _ => form)
  subst before
  obtain ⟨next, exec, same⟩ := JumpBranchSlt.Proofs.rv_comparison_exec hp rowFacts
    (output := ⟨Word.mk (w 50).val (w 51).val, Word.mk (w 30).val (w 31).val⟩) rfl rfl rfl rfl
  rw [rd] at write
  refine ⟨next, exec, same.trans ?_⟩
  exact ⟨rfl, fun k => (write.2.1 k).symm, write.2.2.1.symm, write.2.2.2.1.symm, write.2.2.2.2.symm⟩

/-- Conditional branches. -/
theorem branch_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32}
    {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    (input : JumpBranchSlt.Branch.RVInput) (before : input.before = s)
    (facts : RowFacts words cells epoch w s after entry (JumpBranchSlt.Branch.rvInstruction input))
    (data : entry.data = jumpFields (JumpBranchSlt.Proofs.branchData input))
    (jbs : JumpBranchSlt.rvDecoderFields (JumpBranchSlt.Branch.rvInstruction input) =
      some (JumpBranchSlt.Proofs.branchData input)) :
    RowStep w s after (JumpBranchSlt.Branch.rvInstruction input) := by
  have even := JumpBranchSlt.Proofs.decode_branch_even facts.decodes
  obtain ⟨rowFacts, write⟩ := control_row_facts hp facts data jbs (Or.inr rfl)
    (fun h => absurd h (by simp [JumpBranchSlt.Proofs.branchData]))
  subst before
  obtain ⟨next, exec, same⟩ := JumpBranchSlt.Proofs.rv_branch_exec hp rowFacts even
    (output := ⟨Word.mk (w 50).val (w 51).val, Word.mk (w 30).val (w 31).val⟩) rfl rfl
  refine ⟨next, exec, same.trans ?_⟩
  have zero : (JumpBranchSlt.Proofs.branchData input).rd = 0 := by rfl
  rw [zero] at write
  have quiet := (same_set_zero input.before _).symm.trans write.symm
  exact ⟨rfl, fun k => quiet.2.1 k, quiet.2.2.1, quiet.2.2.2.1, quiet.2.2.2.2⟩

end Airbender.UnifiedReduced.Proofs.RV
