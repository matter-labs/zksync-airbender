import Airbender.Proofs.ReducedMachine.NativeUnifiedLocal
import Airbender.Proofs.ReducedMachine.NativeWordMemoryRetirement
import Airbender.Review.Helpers.Memory.ReducedMachineUnifiedExecution

namespace Airbender.ReducedMachine.NativeUnifiedExecutionProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Fresh actual native GPR address bindings retain EVERY supported-row event.
    This is local to the selected row, not an all-events-GPR mixed-history frame. -/
theorem supported_events {w : Nat → ZMod mersenne31Modulus} {entry : SupportedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (epoch : Nat) :
    ((rowEvents epoch (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).reverse.filter
      fun event => architecturalAddress event.2.1) =
      (rowEvents epoch (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).reverse := by
  apply List.filter_eq_self.mpr
  intro event member
  have present := List.mem_reverse.mp member
  change event ∈ nativeRowEvents epoch importedConstraintsTraceColumns importedConstraintsMemoryPorts w at present
  unfold nativeRowEvents at present
  obtain ⟨port,portMember,rfl⟩ := List.mem_map.mp present
  obtain ⟨code,address⟩ := NativeSupportedLocalProofs.row_register_space ⟨.reduced,w⟩ native fields query port
    (by change port ∈ importedConstraintsMemoryPorts; simpa using portMember)
  change architecturalAddress (port.address.code w) = true
  rw [address]
  simp [architecturalAddress,shadow,Nat.unpair_pair]

/-- Original supported decoding excludes LOAD/STORE; dispatch remains exactly
    the existing original registerClause, without rewriting instruction operands. -/
theorem supported_dispatch [MemoryPlatform SailRV32.exception] {entry : SupportedProgramEntry}
    (fields : supportedDecoderFields entry.instruction = some entry.data) :
    unifiedClause entry.instruction = registerClause entry.instruction := by
  cases instruction : entry.instruction <;> first
    | rfl
    | simp [instruction,supportedDecoderFields,shiftDecoderFields,arithmeticDecoderFields,
        bitwiseDecoderFields,comparisonDecoderFields,branchDecoderFields,jumpDecoderFields] at fields

/-- Actual original word-memory decoding activates only the initial public
    memory-configuration domain, never a desired local permission/success answer. -/
theorem memory_instruction {entry : WordMemoryProgramEntry}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) :
    InstructionUsesWordMemory entry.instruction := by
  unfold wordMemoryDecoderFields at fields
  split at fields
  · rename_i imm rs1 rd instruction
    simp [InstructionUsesWordMemory,instruction]
  · rename_i imm rs2 rs1 instruction
    simp [InstructionUsesWordMemory,instruction]
  · cases fields

theorem memory_dispatch [MemoryPlatform SailRV32.exception] {entry : WordMemoryProgramEntry}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) :
    unifiedClause entry.instruction = wordMemoryClause entry.instruction := by
  unfold wordMemoryDecoderFields at fields
  split at fields
  · rename_i imm rs1 rd instruction
    simp [unifiedClause,instruction]
  · rename_i imm rs2 rs1 instruction
    simp [unifiedClause,instruction]
  · cases fields

end Airbender.ReducedMachine.NativeUnifiedExecutionProofs
