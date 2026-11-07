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
    (query : row.decoderQuery = entry.query) : RowWriteBoundsFromReads row := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with
    ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩
  · exact NativeShiftPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeArithmeticPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeBitwisePreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)
  · exact NativeComparisonPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)

/-- Original x0 decoding and actual masked writes preserve zero across every
    supported native profile. Readonly refreshes and aliases remain in the relation. -/
theorem row_zero_preserving (row : Row mersenne31Modulus NativeReducedFamily) {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowZeroPreserving row := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with
    ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩
  · exact NativeShiftRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeArithmeticRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeBitwiseRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeComparisonRegisterProofs.row_zero_preserving row native selectedFields (query.trans same.symm)

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
      ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩
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

/-- The original supported constructor derives final-PC selection for the
    checked native increment. Alignment remains internal until public decoding. -/
theorem selected_pc_successor {w : Nat → ZMod mersenne31Modulus} {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (aligned : (initialPCWord w).lo % 4 = 0) :
    (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with
    ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩ | ⟨selected,_,selectedFields,same⟩
  · exact NativePCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned
  · exact NativeArithmeticPCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned
  · exact NativeBitwisePCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned
  · exact NativeComparisonPCProofs.selected_pc_successor native selectedFields (query.trans same.symm) aligned

/-- Public original decoding supplies canonical incoming bounds/alignment and
    derives actual bounded PC+4/RV32 rollover without a local PC/carry answer. -/
theorem decoded_pc_successor {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup SupportedMode} {before : State} {count logCapacity : Nat}
    (image : supportedDecoderSetupImage before count logCapacity = some setup)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (initialPCWord w).Bounded ∧ (initialPCWord w).lo % 4 = 0 ∧
      (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec = (initialPCWord w).toBitVec + 4 := by
  obtain ⟨entry,present,source,query⟩ := NativeSupportedDecoderProofs.fetched_sources image native member
  have canonical := native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have aligned : (initialPCWord w).lo % 4 = 0 := by
    rw [canonical]
    exact (run_sparse_setup_sources image present).2
  refine ⟨?_,aligned,selected_pc_successor native source.fields query aligned⟩
  rw [canonical]
  exact Word.ofBitVec_bound _

/-- Invoke checked native local execution only after deriving its actual
    profile/query from the original constructor. Both read ranges are internal
    and are discharged by the common initialized induction. -/
theorem local_row_execution {w : Nat → ZMod mersenne31Modulus} {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (left : (sourceWord w).Bounded)
    (right : (registerOperandWord w).Bounded) (aligned : (w 0).val % 4 = 0)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).reverse before after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord w).toBitVec) := by
  rcases NativeSupportedDecoderProofs.entry_profile fields with
    ⟨selected,instruction,selectedFields,same⟩ | ⟨selected,instruction,selectedFields,same⟩ | ⟨selected,instruction,selectedFields,same⟩ | ⟨selected,instruction,selectedFields,same⟩
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

end Airbender.ReducedMachine.NativeSupportedLocalProofs
