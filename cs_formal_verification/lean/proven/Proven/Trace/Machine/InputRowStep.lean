module
public import Proven.Trace.RVPooled.Oracle
public import Proven.Trace.RVPooled.AddSub
public import Proven.Trace.Machine.InputLift
public import Proven.UnifiedReduced.Modular.Frame

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- An unrolled external read writes the selected independent stream word and consumes it once. -/
theorem unrolled_input_read_step {trace : PooledTrace babyBearModulus} {initial before after : RV.State} {cells : List Cell}
    {w : Nat → ZMod babyBearModulus} {entry : RVPooledProgramEntry} (rd : BitVec 5)
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    (data : entry.data = (rvReadData rd).mapFamily pooledArithmeticFamily)
    (stream tail : List RV.Word)
    (head : stream = (Word.mk (w 33).val (w 34).val).toBitVec :: tail) :
    ∃ next, RV.exec (before.withInput stream) (.inputRead rd) = some next ∧
      RV.Same next ((after.setPC (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).finish.word.toBitVec).withInput tail) := by
  obtain ⟨_, _, written, finish⟩ := rv_addsub_frame (by decide) (by decide) facts data
  let word := (Word.mk (w 33).val (w 34).val).toBitVec
  have same := rv_state_next written rfl finish
  refine ⟨((before.setReg rd word).nextInstr).withInput tail, ?_, same_with_input same tail⟩
  rw [head]
  rfl

/-- An unrolled external write uses NOP metadata and preserves the remaining input stream. -/
theorem unrolled_input_write_step {trace : PooledTrace babyBearModulus} {initial before after : RV.State} {cells : List Cell}
    {w : Nat → ZMod babyBearModulus} {entry : RVPooledProgramEntry} (source : BitVec 5)
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    (data : entry.data = rvNopData.mapFamily pooledArithmeticFamily) :
    RVPooledRowStep ⟨.addSub, w⟩ before after (.inputWrite source) := by
  exact rv_nop_row_step (by decide) (by decide) facts data ⟨_, rfl, RV.Same.refl _⟩

/-- Discarded modular destinations use NOP metadata for every decoded field opcode. -/
theorem unrolled_mop_zero_step {trace : PooledTrace babyBearModulus} {initial before after : RV.State} {cells : List Cell}
    {w : Nat → ZMod babyBearModulus} {entry : RVPooledProgramEntry} (opcode : RV.FieldOp) (rs1 rs2 : BitVec 5)
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    (data : entry.data = rvNopData.mapFamily pooledArithmeticFamily) :
    RVPooledRowStep ⟨.addSub, w⟩ before after (.mop opcode 0 rs1 rs2) := by
  exact rv_nop_row_step (by decide) (by decide) facts data
    ⟨_, RV.exec_mop before opcode 0 rs1 rs2, (rv_same_set_zero before _).nextInstr⟩

/-- A unified external read uses the native destination port and consumes the selected stream head. -/
theorem unified_input_read_step {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {cells : List Cell} {epoch : Nat} {before after : RV.State}
    {entry : UnifiedReduced.RVProgramEntry} (rd : BitVec 5)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (active : w 4 = 1) (query : UnifiedReduced.decoderQuery w = entry.query)
    (data : entry.data = (rvReadData rd).mapFamily (fun _ => UnifiedFamily.machine)) (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after)
    (stream tail : List RV.Word)
    (head : stream = (Word.mk (w 50).val (w 51).val).toBitVec :: tail) :
    ∃ next, RV.exec (before.withInput stream) (.inputRead rd) = some next ∧
      RV.Same next ((after.setPC (Word.mk (w 30).val (w 31).val).toBitVec).withInput tail) := by
  obtain ⟨entryPC, entryBits, entryData⟩ := entry
  change entryData = _ at data
  subst entryData
  have small : ((rvReadData rd).mapFamily (fun _ => UnifiedFamily.machine)).mask < 512 := by
    change (256 : Nat) < 512
    decide
  obtain ⟨_, _, _, _, _, written, finish⟩ := UnifiedReduced.Modular.Proofs.row_frame core active query small pc history
  let word := (Word.mk (w 50).val (w 51).val).toBitVec
  have same := rv_state_next written rfl finish
  refine ⟨((before.setReg rd word).nextInstr).withInput tail, ?_, same_with_input same tail⟩
  rw [head]
  rfl

/-- A unified external write uses the native NOP row and preserves the remaining input. -/
theorem unified_input_write_step {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {cells : List Cell} {epoch : Nat} {before after : RV.State}
    {entry : UnifiedReduced.RVProgramEntry} (source : BitVec 5)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (active : w 4 = 1) (query : UnifiedReduced.decoderQuery w = entry.query)
    (data : entry.data = UnifiedReduced.rvNopFields) (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after) :
    UnifiedReduced.Proofs.RV.RowStep w before after (.inputWrite source) := by
  obtain ⟨entryPC, entryBits, entryData⟩ := entry
  change entryData = _ at data
  subst entryData
  obtain ⟨_, _, _, _, _, written, finish⟩ := UnifiedReduced.Modular.Proofs.row_frame core active query
    (by decide : UnifiedReduced.rvNopFields.mask < 512) pc history
  have same := written.trans (rv_same_set_zero before _)
  exact ⟨_, rfl, rv_state_next same rfl finish⟩

end Airbender.Trace.Machine.Proofs
