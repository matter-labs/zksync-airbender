module
public import Proven.Trace.Machine.UnrolledModularStep
public import Proven.Trace.Machine.UnifiedModularStep

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Discarded modular destinations use the native unrolled NOP row and still take one RV step. -/
theorem unrolled_modular_zero_step {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod babyBearModulus} {before after : RV.State} {entry : RVPooledProgramEntry}
    (opcode : AddSub.Modular.Opcode) (rs1 rs2 : BitVec 5)
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    (dataEq : entry.data = rvNopData.mapFamily pooledArithmeticFamily) :
    RVPooledRowStep ⟨.addSub, w⟩ before after (.mop opcode.rvOp 0 rs1 rs2) := by
  apply rv_nop_row_step (by decide) (by decide) facts dataEq
  exact ⟨_, RV.exec_mop before opcode.rvOp 0 rs1 rs2, (rv_same_set_zero before _).nextInstr⟩

/-- Discarded unified modular destinations use the same public NOP metadata. -/
theorem unified_modular_zero_step {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus} {cells : List Cell} {epoch : Nat}
    {before after : RV.State} {entry : UnifiedReduced.RVProgramEntry}
    (opcode : AddSub.Modular.Opcode) (rs1 rs2 : BitVec 5)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints setup))
    (active : w 4 = 1) (query : UnifiedReduced.decoderQuery w = entry.query)
    (dataEq : entry.data = UnifiedReduced.rvNopFields) (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after) :
    UnifiedReduced.Proofs.RV.RowStep w before after (.mop opcode.rvOp 0 rs1 rs2) := by
  obtain ⟨entryPC, entryBits, entryData⟩ := entry
  change entryData = _ at dataEq
  subst entryData
  obtain ⟨_, _, _, _, _, written, finish⟩ := UnifiedReduced.Modular.Proofs.row_frame core active query
    (by decide : UnifiedReduced.rvNopFields.mask < 512) pc history
  have same := written.trans (rv_same_set_zero before _)
  refine ⟨_, RV.exec_mop before opcode.rvOp 0 rs1 rs2, ?_⟩
  exact (rv_same_set_zero before _).nextInstr.trans (rv_state_next same rfl finish)

end Airbender.Trace.Machine.Proofs
