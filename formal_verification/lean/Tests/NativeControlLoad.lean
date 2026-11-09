import Airbender.Review.Trace.Families.ReducedMachine.ControlLoadTheorems
import Tests.NativeControlShiftJump

namespace Airbender.Tests.NativeControlLoad
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLoad Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure projected metadata/dummy raw bits, not fetched or accepted native rows. -/
private def loadEntry (offset : BitVec 12) (rd : BitVec 5) : WordMemoryProgramEntry :=
  ⟨0,0,.LOAD (offset,.Regidx 1,.Regidx rd,false,4),false,1,0,rd,
    Arithmetic.Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) offset),wordMemoryMask false,2⟩

private def storeEntry : WordMemoryProgramEntry :=
  ⟨0,0,.STORE (0,.Regidx 2,.Regidx 1,4),true,1,2,0,⟨0,0⟩,wordMemoryMask true,2⟩

private def rom (i : Nat) : F :=
  if i = 35 ∨ i = 61 then 16 else if i = 37 then 123 else if i = 43 then 21015 else 0

private def ram (i : Nat) : F :=
  if i = 36 ∨ i = 62 then 64 else if i = 37 ∨ i = 38 ∨ i = 43 ∨ i = 44 then 65535 else 0

theorem original_LW_projection : wordMemoryDecoderFields (loadEntry 0 12).instruction = some (loadEntry 0 12).data := rfl

theorem original_SW_projection : wordMemoryDecoderFields storeEntry.instruction = some storeEntry.data := rfl

theorem SW_dummy_rd : storeEntry.data.rd = 0 := rfl

theorem every_rd12_memory_operation_is_LW {entry : WordMemoryProgramEntry}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (rd : entry.data.rd = 12) :
    entry.data.family = false := Airbender.NativeControlLoadProofs.rd12_load fields rd

theorem ROM_address : addressReference rom (loadEntry 0 12) = ⟨16,0⟩ := by decide +kernel

theorem ROM_value : loadReference rom (loadEntry 0 12) = ⟨21015,0⟩ := by decide +kernel

theorem ROM_shadow_distinct : (Airbender.NativeMainDependencies.read rom 1).word = ⟨123,0⟩ ∧
    loadReference rom (loadEntry 0 12) ≠ (Airbender.NativeMainDependencies.read rom 1).word := by decide +kernel

theorem ROM_ignores_shadow_value : loadReference
    (fun i => if i = 37 ∨ i = 38 then 65535 else rom i) (loadEntry 0 12) = ⟨21015,0⟩ := by decide +kernel

theorem RAM_boundary_address : addressReference ram (loadEntry 0 12) = ⟨0,64⟩ := by decide +kernel

theorem RAM_full_RV32_value : loadReference ram (loadEntry 0 12) = ⟨65535,65535⟩ := by decide +kernel

theorem RAM_reads_actual_second : loadReference ram (loadEntry 0 12) =
    (Airbender.NativeMainDependencies.read ram 1).word := by decide +kernel

theorem ROM_tail_UNIMP : loadReference
    (fun i => if i = 35 then 65532 else if i = 36 then 63 else 0) (loadEntry 0 12) = ⟨4211,49152⟩ := by decide +kernel

theorem sign_extended_negative_offset : addressReference
    (fun i => if i = 35 then 20 else 0) (loadEntry 4092 12) = ⟨16,0⟩ := by decide +kernel

theorem RV32_address_wrap : addressReference
    (fun i => if i = 35 then 65532 else if i = 36 then 65535 else 0) (loadEntry 4 12) = ⟨0,0⟩ := by decide +kernel

theorem wrapped_ROM_value : loadReference
    (fun i => if i = 35 then 65532 else if i = 36 then 65535 else 0) (loadEntry 4 12) = ⟨32947,16⟩ := by decide +kernel

theorem pure_ROM_write : LoadResult rom (loadEntry 0 12) := by
  constructor <;> decide +kernel

theorem pure_RAM_write : LoadResult ram (loadEntry 0 12) := by
  constructor <;> decide +kernel

theorem wrong_shadow_result_rejected : ¬ LoadResult
    (fun i => if i = 43 then 123 else rom i) (loadEntry 0 12) := by
  intro actual
  have wrong : (Airbender.NativeMainDependencies.write (fun i => if i = 43 then 123 else rom i) 2).word ≠
      loadReference (fun i => if i = 43 then 123 else rom i) (loadEntry 0 12) := by decide +kernel
  have written := actual.written
  have nonzero : (loadEntry 0 12).data.rd ≠ 0 := by decide +kernel
  rw [if_neg nonzero] at written
  exact wrong written

theorem load_x0 {w : Nat → F} {entry : WordMemoryProgramEntry} (actual : LoadResult w entry) (zero : entry.data.rd = 0) :
    (Airbender.NativeMainDependencies.write w 2).word = ⟨0,0⟩ := by simpa only [zero,if_true] using actual.written

theorem inactive_CSR_kept : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlShiftJump.inactive_CSR_kept

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
  (effect : Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs)
include effect

theorem every_actual_LW {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {entry : WordMemoryProgramEntry}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query)
    (load : entry.data.family = false) : LoadResult row.assignment entry := effect.loads row member entry fields query load

theorem all_control_edges_same_path : ∃ path, History batch.main.proofs workers inputs path ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path := by
  obtain ⟨path,history,_,csr,arithmetic,bitwise,comparison,shifts,jumps,loads⟩ := effect.path
  exact ⟨path,history,csr,arithmetic,bitwise,comparison,shifts,jumps,loads⟩

theorem nonzero_origins_retained : ∃ path, History batch.main.proofs workers inputs path ∧
    Edges wordMemoryDecoderFields batch.main.proofs path ∧
    ∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token := by
  obtain ⟨path,history,origins,_,_,_,_,_,_,loads⟩ := effect.path
  exact ⟨path,history,loads,origins⟩

theorem prior_shift_jump_retained : Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs := effect.prior

theorem old_logic_retained : Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs := effect.prior.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior
end

theorem full_counted_source {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlLoadProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlLoad
