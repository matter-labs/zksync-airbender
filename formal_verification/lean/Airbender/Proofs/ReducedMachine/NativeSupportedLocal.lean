import Airbender.Review.Helpers.Decoder.ReducedMachineSupported
import Airbender.Proofs.ReducedMachine.NativeSupportedDecoder
import Airbender.Proofs.ReducedMachine.NativeShiftPreservation
import Airbender.Proofs.ReducedMachine.NativeArithmeticPreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.ZeroRegister
import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticZeroRegister
import Airbender.Proofs.ReducedMachine.NativeShiftExecution
import Airbender.Proofs.ReducedMachine.NativeArithmeticExecution
import Airbender.Proofs.ReducedMachine.NativeBitwiseExecution
import Airbender.Proofs.ReducedMachine.NativeBitwisePreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.BitwiseZeroRegister
import Airbender.Proofs.ReducedMachine.NativeComparisonExecution
import Airbender.Proofs.ReducedMachine.NativeComparisonPreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.ComparisonZeroRegister
import Airbender.Proofs.ReducedMachine.NativeBranchExecution
import Airbender.Proofs.ReducedMachine.NativeBranchPreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.BranchZeroRegister

import Airbender.Proofs.ReducedMachine.NativeJumpExecution
import Airbender.Proofs.ReducedMachine.NativeJumpPreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.JumpZeroRegister

namespace Airbender.ReducedMachine.NativeSupportedLocalProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Derive the common local range-induction rule from the original decoded
    profile and its checked actual native equations. Shift lookups use the exact pool. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily) {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) (aligned : row.start.word.lo % 4 = 0) : RowWriteBoundsFromReads row := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with
    ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,pc,bits,instruction,selectedFields,same⟩
  · exact NativeShiftPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeArithmeticPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeBitwisePreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeComparisonPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeBranchPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeJumpPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm) aligned

/-- Original x0 decoding and actual masked writes preserve zero across every
    supported native profile. Readonly refreshes and aliases remain in the relation. -/
theorem row_zero_preserving (row : Row mersenne31Modulus NativeReducedFamily) {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowZeroPreserving row := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with
    ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,pc,bits,instruction,selectedFields,same⟩
  · exact NativeShiftRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeArithmeticRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeBitwiseRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeComparisonRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeBranchRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeJumpRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)

/-- All actual native accesses are register-space accesses for all supported
    profiles; mixed address metadata alone would not establish this. -/
theorem row_register_space (row : Row mersenne31Modulus NativeReducedFamily) {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) (port : MemoryPort) (member : port ∈ row.ports) :
    ∃ code, port.address.code row.assignment = Nat.pair 0 code := by
  cases row with
  | mk family w =>
    cases family
    change port ∈ importedConstraintsMemoryPorts at member
    rcases NativeSupportedDecoderProofs.entry_profile fields with
      ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,pc,bits,instruction,selectedFields,same⟩
    · have addresses := NativeShiftPortProofs.register_addresses native selectedFields (query.trans same.symm)
      simp [importedConstraintsMemoryPorts] at member
      rcases member with rfl | rfl | rfl
      all_goals first | exact ⟨_,addresses 0⟩ | exact ⟨_,addresses 1⟩ | exact ⟨_,addresses 2⟩
    · have addresses := NativeArithmeticPortProofs.register_addresses native selectedFields (query.trans same.symm)
      simp [importedConstraintsMemoryPorts] at member
      rcases member with rfl | rfl | rfl
      all_goals first | exact ⟨_,addresses 0⟩ | exact ⟨_,addresses 1⟩ | exact ⟨_,addresses 2⟩
    · have addresses := NativeBitwisePortProofs.register_addresses native selectedFields (query.trans same.symm)
      simp [importedConstraintsMemoryPorts] at member
      rcases member with rfl | rfl | rfl
      all_goals first | exact ⟨_,addresses 0⟩ | exact ⟨_,addresses 1⟩ | exact ⟨_,addresses 2⟩
    · have addresses := NativeComparisonPortProofs.register_addresses native selectedFields (query.trans same.symm)
      simp [importedConstraintsMemoryPorts] at member
      rcases member with rfl | rfl | rfl
      all_goals first | exact ⟨_,addresses 0⟩ | exact ⟨_,addresses 1⟩ | exact ⟨_,addresses 2⟩
    · have addresses := NativeBranchPortProofs.register_addresses native selectedFields (query.trans same.symm)
      simp [importedConstraintsMemoryPorts] at member
      rcases member with rfl | rfl | rfl
      all_goals first | exact ⟨_,addresses 0⟩ | exact ⟨_,addresses 1⟩ | exact ⟨_,addresses 2⟩
    · have addresses := NativeJumpPortProofs.register_addresses native selectedFields (query.trans same.symm)
      simp [importedConstraintsMemoryPorts] at member
      rcases member with rfl | rfl | rfl
      all_goals first | exact ⟨_,addresses 0⟩ | exact ⟨_,addresses 1⟩ | exact ⟨_,addresses 2⟩

/-- Original decoded BTYPE parity transports through the common projection.
    No supplied per-row offset/parity answer is needed. -/
theorem branch_offset_even {w : Nat → ZMod mersenne31Modulus}
    {entry : SupportedProgramEntry} {selected : BranchProgramEntry} {initial : State}
    (source : entry.SourceWith initial supportedDecoderFields)
    (instruction : selected.instruction = entry.instruction)
    (fields : branchDecoderFields selected.instruction = some selected.data)
    (query : decoderQuery w = selected.query) : (branchOffsetWord w).lo % 2 = 0 := by
  let original : BranchProgramEntry := ⟨entry.pc,entry.bits,entry.instruction,selected.data⟩
  have fetched : original.SourceWith initial branchDecoderFields :=
    ⟨source.bytes,source.decoded,by simpa only [instruction] using fields⟩
  rw [NativeBranchDecoderProofs.immediate_word fields query]
  exact NativeBranchDecoderProofs.offset_even (entry := original) fetched

/-- Actual final-PC bounds follow operation-specific native semantics. Ordinary
    PC+4 proofs stay unchanged; branches use their checked conditional effects. -/
theorem selected_pc_bound {w : Nat → ZMod mersenne31Modulus} {entry : SupportedProgramEntry}
    {initial : State}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (source : entry.SourceWith initial supportedDecoderFields)
    (query : decoderQuery w = entry.query) (left : (sourceWord w).Bounded)
    (right : (registerOperandWord w).Bounded) (aligned : (initialPCWord w).lo % 4 = 0) :
    (finalPCWord w).Bounded := by
  rcases NativeSupportedDecoderProofs.entry_profile source.fields with
    ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,_,selectedFields,same⟩ |
    ⟨selected,_,_,_,selectedFields,same⟩ | ⟨selected,_,_,instruction,selectedFields,same⟩ | ⟨selected,pc,bits,instruction,selectedFields,same⟩
  · exact (NativePCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned).1
  · exact (NativeArithmeticPCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned).1
  · exact (NativeBitwisePCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned).1
  · exact (NativeComparisonPCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned).1
  · have branchQuery := query.trans same.symm
    have decoded := NativeBranchDecoderProofs.decoded_fields selectedFields branchQuery
    have tagBound : branchFunct3 selected.data.family < mersenne31Modulus := by
      cases selected.data.family <;> decide
    have tags : (w 11).val ∈ [0,1,4,5,6,7] := by
      rw [decoded.funct3,ZMod.val_natCast_of_lt tagBound]
      exact NativeBranchDecoderProofs.tags _
    have canonical := native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
    change initialPCWord w = Word.ofBitVec entry.pc at canonical
    have pc : (initialPCWord w).Bounded := by rw [canonical]; exact Word.ofBitVec_bound _
    have offset : (branchOffsetWord w).Bounded := by
      rw [NativeBranchDecoderProofs.immediate_word selectedFields branchQuery]
      exact (NativeBranchDecoderProofs.field_bounds selectedFields).1
    have routing := NativeBranchFieldProofs.source native decoded.mask
    have lo := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) routing
    have hi := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) routing
    change w 47 = w 37 at lo
    change w 48 = w 38 at hi
    have operand : operandWord w = registerOperandWord w := by
      simp [operandWord,registerOperandWord,source2,lo,hi,importedConstraintsMemoryPorts,WordColumns.evaluate]
    have selectedBound : (operandWord w).Bounded := by rw [operand]; exact right
    exact (NativeBranchPCProofs.effects native decoded.mask tags left selectedBound pc offset aligned
      (branch_offset_even source instruction selectedFields branchQuery)).1
  · have decoded := NativeJumpDecoderProofs.decoded_fields selectedFields (query.trans same.symm)
    exact (NativeJumpNumericalProofs.final_bounds native selected.data.family decoded.mask).1

/-- Complete original public membership supplies canonical incoming bounds and
    alignment. It does not assert a universal PC+4 for conditional control flow. -/
theorem decoded_pc_inputs {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup SupportedMode} {before : State} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage before count logCapacity = some setup)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (initialPCWord w).Bounded ∧ (initialPCWord w).lo % 4 = 0 := by
  obtain ⟨entry,present,source,query⟩ := NativeSupportedDecoderProofs.fetched_sources image native member
  have canonical := native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  rw [canonical]
  exact ⟨Word.ofBitVec_bound _,(run_sparse_setup_sources image present).2⟩

/-- Invoke checked native local execution only after deriving its actual
    profile/query from the original constructor. Both read ranges are internal
    and are discharged by the common initialized induction. -/
theorem local_row_execution {w : Nat → ZMod mersenne31Modulus} {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    {initial : State} (source : entry.SourceWith initial supportedDecoderFields)
    (query : decoderQuery w = entry.query) (left : (sourceWord w).Bounded)
    (right : (registerOperandWord w).Bounded) (aligned : (w 0).val % 4 = 0)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).reverse before after)
    (isa : InstructionUsesMisa entry.instruction → ∃ value, before.regs.get? .misa = some value)
    (configuration : (∃ args, entry.instruction = .JALR args) →
      before.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
        before.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord w).toBitVec) := by
  rcases NativeSupportedDecoderProofs.entry_profile source.fields with
    ⟨selected,_,_,instruction,selectedFields,same⟩ | ⟨selected,_,_,instruction,selectedFields,same⟩ | ⟨selected,_,_,instruction,selectedFields,same⟩ | ⟨selected,_,_,instruction,selectedFields,same⟩ | ⟨selected,_,_,instruction,selectedFields,same⟩ | ⟨selected,pc,bits,instruction,selectedFields,same⟩
  · obtain ⟨clause,dispatch,execute⟩ := NativeShiftExecutionProofs.local_row_execution native selectedFields
      (query.trans same.symm) left aligned epoch history
    exact ⟨clause,by simpa only [instruction] using dispatch,execute⟩
  · obtain ⟨clause,dispatch,execute⟩ := NativeArithmeticExecutionProofs.local_row_execution native selectedFields
      (query.trans same.symm) left right aligned epoch history
    exact ⟨clause,by simpa only [instruction] using dispatch,execute⟩
  · obtain ⟨clause,dispatch,execute⟩ := NativeBitwiseExecutionProofs.local_row_execution native selectedFields
      (query.trans same.symm) aligned epoch history
    exact ⟨clause,by simpa only [instruction] using dispatch,execute⟩
  · obtain ⟨clause,dispatch,execute⟩ := NativeComparisonExecutionProofs.local_row_execution native selectedFields
      (query.trans same.symm) left right aligned epoch history
    exact ⟨clause,by simpa only [instruction] using dispatch,execute⟩


  · have even := branch_offset_even source instruction selectedFields (query.trans same.symm)
    obtain ⟨opcode,imm,rs1,rs2,shape⟩ := NativeBranchClauseProofs.encoding selectedFields
    have readable := isa (by rw [← instruction,shape]; trivial)
    obtain ⟨clause,dispatch,execute⟩ := NativeBranchExecutionProofs.local_row_execution native selectedFields
      (query.trans same.symm) left right aligned even epoch history readable
    exact ⟨clause,by simpa only [instruction] using dispatch,execute⟩

  · have fetched : selected.SourceWith initial jumpDecoderFields :=
      ⟨by simpa only [pc,bits] using source.bytes,
        by simpa only [bits,instruction] using source.decoded,selectedFields⟩
    obtain ⟨operation,rs1,rd,encoded⟩ := NativeJumpExecutionProofs.encoding selectedFields
    have readable := isa (by rw [← instruction,encoded]; cases operation <;> trivial)
    have configured : selected.data.family = false → before.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, before.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0 := by
      intro indirect
      obtain ⟨args,shape⟩ := NativeJumpExecutionProofs.indirect_encoding selectedFields indirect
      exact configuration ⟨args,instruction.symm.trans shape⟩
    obtain ⟨clause,dispatch,execute⟩ := NativeJumpExecutionProofs.local_row_execution native fetched
      (query.trans same.symm) left aligned epoch history readable configured
    exact ⟨clause,by simpa only [instruction] using dispatch,execute⟩

end Airbender.ReducedMachine.NativeSupportedLocalProofs
