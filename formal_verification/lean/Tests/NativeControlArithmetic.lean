import Airbender.Review.Trace.Families.ReducedMachine.ControlArithmeticTheorems
import Tests.NativeControlCSR

namespace Airbender.Tests.NativeControlArithmetic
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlArithmetic
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure finite reference data, not an accepted native BODY or global witness. -/
private def entry (mode : ArithmeticMode) : ArithmeticProgramEntry :=
  let instruction := match mode with
    | .add => SailRV32.instruction.RTYPE (.Regidx 2,.Regidx 1,.Regidx 12,.ADD)
    | .addi => .ITYPE (4095,.Regidx 1,.Regidx 12,.ADDI)
    | .sub => .RTYPE (.Regidx 2,.Regidx 1,.Regidx 12,.SUB)
    | .lui => .UTYPE (1048575,.Regidx 12,.LUI)
    | .auipc => .UTYPE (1048575,.Regidx 12,.AUIPC)
  let immediate : BitVec 32 := match mode with
    | .addi => 4294967295
    | .lui | .auipc => 4294963200
    | _ => 0
  let rs1 : BitVec 5 := match mode with | .lui | .auipc => 0 | _ => 1
  let rs2 : BitVec 5 := if mode.useRegister then 2 else 0
  let funct3 : Nat := match mode with | .lui | .auipc => 7 | _ => 0
  ⟨4294967292,0,instruction,mode,rs1,rs2,12,Arithmetic.Word.ofBitVec immediate,mode.mask,funct3⟩

private def assignment (i : Nat) : F :=
  if i = 35 ∨ i = 36 then 65535 else if i = 37 then 1 else 0

theorem original_projection (mode : ArithmeticMode) :
    arithmeticDecoderFields (entry mode).instruction = some (entry mode).data := by
  cases mode <;> rfl

theorem add_wrap : reference assignment (entry .add) = 0 := by decide +kernel
theorem addi_immediate : reference assignment (entry .addi) = 4294967294 := by decide +kernel
theorem sub_wrap : reference assignment (entry .sub) = 4294967294 := by decide +kernel
theorem lui_full_RV32 : reference assignment (entry .lui) = 4294963200 := by decide +kernel
theorem auipc_wrap : reference assignment (entry .auipc) = 4294963196 := by decide +kernel

theorem old_control_ignored : reference (fun i => if i = 41 ∨ i = 42 then 65535 else assignment i) (entry .add) = 0 := by decide +kernel

theorem addi_keeps_unused_second_read :
    reference (fun i => if i = 37 ∨ i = 38 then 65535 else assignment i) (entry .addi) = 4294967294 := by decide +kernel

theorem x12_write_reference : Result assignment (entry .add) := by unfold Result; decide +kernel

theorem wrong_high_rejected : ¬ Result (fun i => if i = 44 then 1 else assignment i) (entry .add) := by unfold Result; decide +kernel

theorem x0_mask {w : Nat → F} {selected : ArithmeticProgramEntry}
    (actual : Result w selected) (zero : selected.data.rd = 0) :
    (Airbender.NativeMainDependencies.write w 2).word = ⟨0,0⟩ := by
  simpa [Result,zero] using actual

theorem rd12_both_limbs {w : Nat → F} {selected : ArithmeticProgramEntry}
    (actual : Result w selected) (rd : selected.data.rd = 12) :
    limbs (Airbender.NativeMainDependencies.write w 2) =
      ((Arithmetic.Word.ofBitVec (reference w selected)).lo,(Arithmetic.Word.ofBitVec (reference w selected)).hi) :=
  Airbender.NativeControlArithmeticProofs.rd12_limbs actual rd

theorem actual_read_ABI (w : Nat → F) :
    (Airbender.NativeMainDependencies.read w 0).word = sourceWord w ∧
    (Airbender.NativeMainDependencies.read w 1).word = registerOperandWord w :=
  Airbender.NativeControlArithmeticProofs.read_words w

theorem actual_write_ABI (w : Nat → F) : (Airbender.NativeMainDependencies.write w 2).word = writtenWord w :=
  Airbender.NativeControlArithmeticProofs.write_word w

theorem inactive_CSR_kept :
    limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  Airbender.Tests.NativeControlCSR.inactive_clear_retained

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
  (effect : Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs)
include effect

theorem every_actual_arithmetic {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {selected : ArithmeticProgramEntry}
    (fields : arithmeticDecoderFields selected.instruction = some selected.data) (query : row.decoderQuery = selected.query) :
    Result row.assignment selected := effect.arithmetic row member selected fields query

theorem arithmetic_CSR_same_path : ∃ path, History batch.main.proofs workers inputs path ∧ Edges batch.main.proofs path ∧
    (∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ selected : CSRProgramEntry,
      csrDecoderFields selected.instruction = some selected.data → row.decoderQuery = selected.query → selected.data.rd = 12 →
      (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail) := by
  obtain ⟨path,history,_,csr,arithmetic⟩ := effect.path
  exact ⟨path,history,arithmetic,csr⟩

theorem nonzero_origins_same_path : ∃ path, History batch.main.proofs workers inputs path ∧ Edges batch.main.proofs path ∧
    ∀ token ∈ path, (limbs token).2 ≠ 0 → Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs token := by
  obtain ⟨path,history,origins,_,arithmetic⟩ := effect.path
  exact ⟨path,history,arithmetic,origins⟩

theorem prior_CSR_retained : Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs := effect.prior

theorem old_history_retained : Airbender.NativeControlHistory.Effects batch workers inputs := effect.prior.prior.prior

theorem old_counts_retained : Airbender.NativeCallerCount.Effects batch workers inputs := effect.prior.prior.prior.prior.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior.prior.prior
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
    Airbender.NativeControlArithmetic.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlArithmeticProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlArithmetic
