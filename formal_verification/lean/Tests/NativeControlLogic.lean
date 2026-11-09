import Airbender.Review.Trace.Families.ReducedMachine.ControlLogicTheorems
import Tests.NativeControlCSR

namespace Airbender.Tests.NativeControlLogic
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure original metadata with dummy raw bits, not a fetched/accepted fixture. -/
private def bitwiseEntry (kind : Verification.BinaryKind) (form : Bool) : BitwiseProgramEntry :=
  let instruction := if form then SailRV32.instruction.RTYPE
    (.Regidx 2,.Regidx 1,.Regidx 12,match kind with | .xor => .XOR | .or => .OR | .and => .AND)
    else .ITYPE (4095,.Regidx 1,.Regidx 12,match kind with | .xor => .XORI | .or => .ORI | .and => .ANDI)
  ⟨0,0,instruction,⟨kind,form⟩,1,(if form then 2 else 0),12,
    Arithmetic.Word.ofBitVec (if form then 0 else 4294967295),bitwiseMask form,kind.tag⟩

private def comparisonEntry (signed form : Bool) : ComparisonProgramEntry :=
  let instruction := if form then SailRV32.instruction.RTYPE
    (.Regidx 2,.Regidx 1,.Regidx 12,if signed then .SLT else .SLTU)
    else .ITYPE (4095,.Regidx 1,.Regidx 12,if signed then .SLTI else .SLTIU)
  ⟨0,0,instruction,⟨signed,form⟩,1,(if form then 2 else 0),12,
    Arithmetic.Word.ofBitVec (if form then 0 else 4294967295),comparisonMask form,if signed then 2 else 3⟩

private def assignment (i : Nat) : F := if i = 36 then 32768 else if i = 37 then 1 else 0

theorem original_bitwise_projection (kind : Verification.BinaryKind) (form : Bool) :
    bitwiseDecoderFields (bitwiseEntry kind form).instruction = some (bitwiseEntry kind form).data := by
  cases kind <;> cases form <;> rfl

theorem original_comparison_projection (signed form : Bool) :
    comparisonDecoderFields (comparisonEntry signed form).instruction = some (comparisonEntry signed form).data := by
  cases signed <;> cases form <;> rfl

theorem xor_register : bitwiseReference assignment (bitwiseEntry .xor true) = 2147483649 := by decide +kernel
theorem or_register : bitwiseReference assignment (bitwiseEntry .or true) = 2147483649 := by decide +kernel
theorem and_register : bitwiseReference assignment (bitwiseEntry .and true) = 0 := by decide +kernel
theorem xor_immediate : bitwiseReference assignment (bitwiseEntry .xor false) = 2147483647 := by decide +kernel
theorem or_immediate : bitwiseReference assignment (bitwiseEntry .or false) = 4294967295 := by decide +kernel
theorem and_immediate : bitwiseReference assignment (bitwiseEntry .and false) = 2147483648 := by decide +kernel

theorem signed_register : comparisonReference assignment (comparisonEntry true true) = 1 := by decide +kernel
theorem unsigned_register : comparisonReference assignment (comparisonEntry false true) = 0 := by decide +kernel
theorem signed_immediate : comparisonReference assignment (comparisonEntry true false) = 1 := by decide +kernel
theorem unsigned_immediate : comparisonReference assignment (comparisonEntry false false) = 1 := by decide +kernel

theorem immediate_retains_unused_read : bitwiseReference
    (fun i => if i = 37 ∨ i = 38 then 65535 else assignment i) (bitwiseEntry .xor false) = 2147483647 := by decide +kernel

theorem old_control_ignored : comparisonReference
    (fun i => if i = 41 ∨ i = 42 then 65535 else assignment i) (comparisonEntry false true) = 0 := by decide +kernel

theorem pure_and_write : BitwiseResult assignment (bitwiseEntry .and true) := by unfold BitwiseResult; decide +kernel

theorem pure_unsigned_write : ComparisonResult assignment (comparisonEntry false true) := by unfold ComparisonResult; decide +kernel

theorem wrong_comparison_high_rejected : ¬ ComparisonResult
    (fun i => if i = 44 then 1 else assignment i) (comparisonEntry false true) := by unfold ComparisonResult; decide +kernel

theorem every_comparison_high_zero {w : Nat → F} {entry : ComparisonProgramEntry} (actual : ComparisonResult w entry) :
    (limbs (Airbender.NativeMainDependencies.write w 2)).2 = 0 := Airbender.NativeControlLogicProofs.comparison_high actual

theorem comparison_cannot_seed_high {w : Nat → F} {entry : ComparisonProgramEntry} (actual : ComparisonResult w entry) :
    ¬ (limbs (Airbender.NativeMainDependencies.write w 2)).2 ≠ 0 := by
  exact not_not_intro (Airbender.NativeControlLogicProofs.comparison_high actual)

theorem bitwise_x0 {w : Nat → F} {entry : BitwiseProgramEntry} (actual : BitwiseResult w entry) (zero : entry.data.rd = 0) :
    (Airbender.NativeMainDependencies.write w 2).word = ⟨0,0⟩ := by simpa [BitwiseResult,zero] using actual

theorem comparison_x0 {w : Nat → F} {entry : ComparisonProgramEntry} (actual : ComparisonResult w entry) (zero : entry.data.rd = 0) :
    (Airbender.NativeMainDependencies.write w 2).word = ⟨0,0⟩ := by simpa [ComparisonResult,zero] using actual

theorem inactive_CSR_kept : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlCSR.inactive_clear_retained

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
  (effect : Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs)
include effect

theorem every_actual_bitwise {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {entry : BitwiseProgramEntry}
    (fields : bitwiseDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query) :
    BitwiseResult row.assignment entry := effect.bitwise row member entry fields query

theorem every_actual_comparison {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {entry : ComparisonProgramEntry}
    (fields : comparisonDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query) :
    ComparisonResult row.assignment entry ∧ (limbs (Airbender.NativeMainDependencies.write row.assignment 2)).2 = 0 :=
  effect.comparison row member entry fields query

theorem all_logic_arithmetic_CSR_same_path : ∃ path, History batch.main.proofs workers inputs path ∧
    Edges csrDecoderFields batch.main.proofs path ∧ Airbender.NativeControlArithmetic.Edges batch.main.proofs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path := by
  obtain ⟨path,history,_,csr,arithmetic,bitwise,comparison⟩ := effect.path
  exact ⟨path,history,csr,arithmetic,bitwise,comparison⟩

theorem nonzero_origins_retained : ∃ path, History batch.main.proofs workers inputs path ∧
    Edges bitwiseDecoderFields batch.main.proofs path ∧ Edges comparisonDecoderFields batch.main.proofs path ∧
    ∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token := by
  obtain ⟨path,history,origins,_,_,bitwise,comparison⟩ := effect.path
  exact ⟨path,history,bitwise,comparison,origins⟩

theorem prior_arithmetic_retained : Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs := effect.prior

theorem old_CSR_retained : Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs := effect.prior.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior.prior.prior.prior
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
    Airbender.NativeControlLogic.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlLogicProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlLogic
