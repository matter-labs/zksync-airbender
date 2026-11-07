import Airbender.Proofs.Reduced.ArithmeticExecution

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Trace.Proofs
open AddSub.Modular.External.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Shift and bitwise clauses use the zero reads of the shared architecture. -/
theorem shift_execution_from_shared_history
    (hp : FieldCapacity.NativeWordCapacity babyBearModulus)
    (inverse : SerializedInverse.Clock babyBearModulus)
    {initial before after : State} {cells : List Cell}
    {w : Nat → ZMod babyBearModulus} {entry : PooledProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ShiftBinop.importedConstraints)
    (active : w ShiftBinop.importedConstraintsTraceColumns.execute = 1)
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .shiftBinop) (query : ShiftBinop.decoderQuery w = entry.query)
    (zeros : ∀ port ∈ ShiftBinop.importedConstraintsMemoryPorts,
      port.address.code w = (Cell.register 0).addressCode → (readToken w port).value = 0)
    (epoch : Nat)
    (history : SailHistory cells (ShiftBinop.Proofs.nativeEvents epoch w).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  obtain original | original | original | original | original := source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · rw [mapped_query] at query
    have arithmeticInverse : SerializedInverse.Limb16 babyBearModulus := by
      calc
        (-30720 : ZMod babyBearModulus) * 65536 = (-3840 : ZMod babyBearModulus) * 524288 := by ring
        _ = 1 := inverse
    exact ShiftBinop.Proofs.local_instruction_execution hp arithmeticInverse core active
      epoch originalSource query zeros history
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

/-- Branch, jump and comparison clauses use the actual shared operand history.
The native PC adapter must supply alignment and the final high-limb range. -/
theorem control_execution_from_shared_history
    (hp : FieldCapacity.NativeWordCapacity babyBearModulus)
    {initial before after : State} {cells : List Cell} {events : List MemoryAccess}
    {w : Nat → ZMod babyBearModulus} {entry : PooledProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      JumpBranchSlt.importedConstraints)
    (active : w JumpBranchSlt.importedConstraintsTraceColumns.execute = 1)
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .jumpBranchSlt) (query : JumpBranchSlt.decoderQuery w = entry.query)
    (leftBound : (Word.mk (w 22).val (w 23).val).Bounded)
    (rightBound : (Word.mk (w 26).val (w 27).val).Bounded)
    (aligned : (w 0).val % 4 = 0) (finalHi : (w 17).val < limbBase)
    (epoch : Nat) (past : SailHistory cells events initial before)
    (history : SailHistory cells (JumpBranchSlt.Proofs.nativeEvents epoch w).reverse before after)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 16).val (w 17).val).toBitVec) := by
  obtain original | original | original | original | original := source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · rw [mapped_query] at query
    exact JumpBranchSlt.Proofs.local_instruction_execution (by omega) core active
      epoch originalSource query leftBound rightBound aligned finalHi history past isa configuration
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.AddSub.Modular.External.Caller.Proofs
