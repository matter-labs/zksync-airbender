import Airbender.Review.Trace.Families.ReducedMachine.ControlShiftJumpTheorems
import Tests.NativeControlLogic

namespace Airbender.Tests.NativeControlShiftJump
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlShiftJump Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure projected metadata with dummy raw bits, not a fetched/native witness. -/
private def shiftEntry (mode : ShiftMode) (form : Bool) (amount : Nat) : ShiftProgramEntry :=
  let instruction := if form then SailRV32.instruction.RTYPE
    (.Regidx 2,.Regidx 1,.Regidx 12,match mode with | .left => .SLL | .right => .SRL | .arithmetic => .SRA)
    else .SHIFTIOP (BitVec.ofNat 6 amount,.Regidx 1,.Regidx 12,
      match mode with | .left => .SLLI | .right => .SRLI | .arithmetic => .SRAI)
  ⟨0,0,instruction,mode,1,(if form then 2 else 0),12,
    Arithmetic.Word.ofBitVec (BitVec.ofNat 32 (if form then 0 else if mode = .arithmetic then amount+1024 else amount)),
    mode.mask form,mode.funct3⟩

private def jumpEntry (jal : Bool) (pc : BitVec 32) : JumpProgramEntry :=
  ⟨pc,0,(if jal then .JAL (0,.Regidx 12) else .JALR (0,.Regidx 1,.Regidx 12)),jal,
    (if jal then 0 else 1),0,12,⟨0,0⟩,jumpMask jal,0⟩

private def assignment (i : Nat) : F :=
  if i = 35 then 1 else if i = 36 then 32768 else if i = 37 then 63 else 0

theorem all_six_original_shift_projections (mode : ShiftMode) (form : Bool) :
    shiftDecoderFields (shiftEntry mode form 1).instruction = some (shiftEntry mode form 1).data := by
  cases mode <;> cases form <;> rfl

theorem original_jump_projections (jal : Bool) :
    jumpDecoderFields (jumpEntry jal 0).instruction = some (jumpEntry jal 0).data := by cases jal <;> rfl

theorem invalid_immediate_rejected : shiftDecoderFields
    (.SHIFTIOP (32,.Regidx 1,.Regidx 12,.SRAI)) = none := by decide +kernel

theorem register_left_masks_amount : shiftReference assignment (shiftEntry .left true 0) = 2147483648 := by decide +kernel
theorem register_right_masks_amount : shiftReference assignment (shiftEntry .right true 0) = 1 := by decide +kernel
theorem register_arithmetic_masks_amount : shiftReference assignment (shiftEntry .arithmetic true 0) = 4294967295 := by decide +kernel

theorem immediate_left : shiftReference assignment (shiftEntry .left false 1) = 2 := by decide +kernel
theorem immediate_right : shiftReference assignment (shiftEntry .right false 1) = 1073741824 := by decide +kernel
theorem immediate_arithmetic : shiftReference assignment (shiftEntry .arithmetic false 1) = 3221225472 := by decide +kernel

theorem encoded_SRAI_1055 : shiftReference assignment (shiftEntry .arithmetic false 31) = 4294967295 := by decide +kernel

theorem immediate_retains_irrelevant_rs2 : shiftReference
    (fun i => if i = 37 ∨ i = 38 then 65535 else assignment i) (shiftEntry .right false 1) = 1073741824 := by decide +kernel

theorem old_control_ignored : shiftReference
    (fun i => if i = 41 ∨ i = 42 then 65535 else assignment i) (shiftEntry .arithmetic true 0) = 4294967295 := by decide +kernel

theorem full_RV32_shift_write : ShiftResult
    (fun i => if i = 43 ∨ i = 44 then 65535 else assignment i) (shiftEntry .arithmetic true 0) := by
  unfold ShiftResult; decide +kernel

theorem wrong_shift_high_rejected : ¬ ShiftResult
    (fun i => if i = 43 then 65535 else assignment i) (shiftEntry .arithmetic true 0) := by
  unfold ShiftResult; decide +kernel

theorem jump_RV32_wrap (jal : Bool) : JumpResult assignment (jumpEntry jal 4294967292) := by
  cases jal <;> unfold JumpResult <;> decide +kernel

theorem jump_full_RV32_link (jal : Bool) : JumpResult
    (fun i => if i = 43 then 4 else if i = 44 then 32768 else assignment i) (jumpEntry jal 2147483648) := by
  cases jal <;> unfold JumpResult <;> decide +kernel

theorem jump_target_not_link (jal : Bool) : ¬ JumpResult assignment (jumpEntry jal 0) := by
  cases jal <;> unfold JumpResult <;> decide +kernel

theorem shift_x0 {w : Nat → F} {entry : ShiftProgramEntry} (actual : ShiftResult w entry) (zero : entry.data.rd = 0) :
    (Airbender.NativeMainDependencies.write w 2).word = ⟨0,0⟩ := by simpa [ShiftResult,zero] using actual

theorem jump_x0 {w : Nat → F} {entry : JumpProgramEntry} (actual : JumpResult w entry) (zero : entry.data.rd = 0) :
    (Airbender.NativeMainDependencies.write w 2).word = ⟨0,0⟩ := by simpa [JumpResult,zero] using actual

theorem inactive_CSR_kept : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlLogic.inactive_CSR_kept

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
  (effect : Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs)
include effect

theorem every_actual_shift {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {entry : ShiftProgramEntry}
    (fields : shiftDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query) :
    ShiftResult row.assignment entry := effect.shifts row member entry fields query

theorem every_actual_jump {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {entry : JumpProgramEntry}
    (fields : jumpDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query) :
    JumpResult row.assignment entry := effect.jumps row member entry fields query

theorem all_control_edges_same_path : ∃ path, History batch.main.proofs workers inputs path ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path := by
  obtain ⟨path,history,_,csr,arithmetic,bitwise,comparison,shifts,jumps⟩ := effect.path
  exact ⟨path,history,csr,arithmetic,bitwise,comparison,shifts,jumps⟩

theorem nonzero_origins_retained : ∃ path, History batch.main.proofs workers inputs path ∧
    Edges shiftDecoderFields batch.main.proofs path ∧ Edges jumpDecoderFields batch.main.proofs path ∧
    ∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token := by
  obtain ⟨path,history,origins,_,_,_,_,shifts,jumps⟩ := effect.path
  exact ⟨path,history,shifts,jumps,origins⟩

theorem old_logic_retained : Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs := effect.prior

theorem old_arithmetic_retained : Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs := effect.prior.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior.prior.prior.prior.prior
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
    Airbender.NativeControlShiftJump.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlShiftJumpProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlShiftJump
