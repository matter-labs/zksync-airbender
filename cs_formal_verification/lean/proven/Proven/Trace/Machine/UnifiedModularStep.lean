module
public import Proven.Trace.Machine.ModularWords
public import Proven.Trace.RVPooledStep
public import Proven.UnifiedReduced.Modular.Frame
public import Proven.UnifiedReduced.Modular.Result

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A native unified modular row executes its RV field instruction without an ordinary-projection premise. -/
theorem unified_modular_row_step {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {cells : List Cell} {epoch : Nat}
    {before after : RV.State} {entry : UnifiedReduced.RVProgramEntry}
    (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) (nonzero : rd ≠ 0)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (active : w 4 = 1) (query : UnifiedReduced.decoderQuery w = entry.query)
    (dataEq : entry.data = (modularData opcode rs1 rs2 rd).mapFamily (fun _ => UnifiedFamily.machine))
    (pc : before.pc = entry.pc)
    (leftBound : (Word.mk (w 36).val (w 37).val).Bounded)
    (rightBound : (Word.mk (w 42).val (w 43).val).Bounded)
    (oldBound : (Word.mk (w 48).val (w 49).val).Bounded)
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after) :
    UnifiedReduced.Proofs.RV.RowStep w before after (.mop opcode.rvOp rd rs1 rs2) := by
  obtain ⟨entryPC, entryBits, entryData⟩ := entry
  change entryData = _ at dataEq
  subst entryData
  have small : ((modularData opcode rs1 rs2 rd).mapFamily (fun _ => UnifiedFamily.machine)).mask < 128 := by
    cases opcode <;> norm_num [modularData, AddSub.Modular.Opcode.selector, DecoderData.mapFamily]
  obtain ⟨flags, noTriAdd, left, right, old, written, finish⟩ :=
    UnifiedReduced.Modular.Proofs.row_frame core active query small pc history
  have pcWord := rv_native_query_pc_word (by decide : limbBase < babyBearModulus) query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entryPC at pcWord
  have rdQuery := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
  change w 7 = (rd.toNat : ZMod babyBearModulus) at rdQuery
  let input := modularInput opcode rs1 rs2 rd before
  let output : Circuit.Output := ⟨⟨(w 50).val, (w 51).val⟩, ⟨(w 30).val, (w 31).val⟩⟩
  have interfaces : AddSub.Modular.InterfaceAssumptions input output (UnifiedReduced.Modular.Proofs.lift w) := by
    refine ⟨active, ?_, Word.ofBitVec_bound _⟩
    intro k lower upper
    have flag := flags ⟨k - 10, by omega⟩
    have column : UnifiedReduced.Modular.Proofs.lift w k = w (11 + (k - 10)) := by interval_cases k <;> rfl
    change w (11 + (k - 10)) = if (modularData opcode rs1 rs2 rd).mask.testBit (k - 10) then 1 else 0 at flag
    rw [modular_mask_bit opcode rs1 rs2 rd k lower upper] at flag
    rw [column]
    simpa only [input, modularInput, ite_eq_right nonzero, decide_eq_true_eq] using flag
  have mapping : AddSub.Modular.WordMapping input output (UnifiedReduced.Modular.Proofs.lift w) := by
    refine ⟨?_, ?_, ?_, rdQuery, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · intro _
      exact modular_word_residue leftBound left
    · intro _
      exact modular_word_residue rightBound right
    · intro _ _
      exact modular_word_residue oldBound old
    · change w 0 = ((Word.ofBitVec before.pc).lo : ZMod babyBearModulus)
      rw [pc, ← pcWord, ZMod.natCast_zmod_val]
    · change w 1 = ((Word.ofBitVec before.pc).hi : ZMod babyBearModulus)
      rw [pc, ← pcWord, ZMod.natCast_zmod_val]
  have result := UnifiedReduced.Modular.Proofs.modular_result core noTriAdd interfaces mapping nonzero
  have value : output.destination.toBitVec =
      RV.mopVal opcode.rvOp (before.getReg rs1) (before.getReg rs2) (before.getReg rd) := by
    change BitVec.ofNat 32 output.destination.value = _
    rw [result, AddSub.Modular.arithmeticResult_rv]
    rfl
  refine ⟨_, RV.exec_mop before opcode.rvOp rd rs1 rs2, ?_⟩
  rw [← value]
  exact rv_state_next written rfl finish

end Airbender.Trace.Machine.Proofs
