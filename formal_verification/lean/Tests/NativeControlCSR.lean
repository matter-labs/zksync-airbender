import Airbender.Review.Trace.Families.ReducedMachine.ControlCSRTheorems
import Tests.NativeCSRPositive

namespace Airbender.Tests.NativeControlCSR
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlCSR
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Reuse the old complete LOCAL BODY, not a new global accepted witness. -/
theorem local_result (active : Bool) : CSRResult (NativeCSRPositiveWitness.assignment active) Airbender.Tests.NativeCSRPositive.entry := by
  apply Airbender.NativeControlCSRProofs.result (NativeCSRPositiveWitness.body active) rfl
  cases active <;> decide +kernel

theorem local_delegation_clear (active : Bool) :
    limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment active) 2) = (0,0) :=
  (local_result active).clear rfl

theorem inactive_clear_retained : limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment false) 2) = (0,0) :=
  local_delegation_clear false

theorem local_wrong_nonzero_rejected (active : Bool) :
    (limbs (Airbender.NativeMainDependencies.write (NativeCSRPositiveWitness.assignment active) 2)).2 ≠ 8 := by
  rw [local_delegation_clear]
  decide +kernel

theorem x0_clear {w : Nat → F} {entry : CSRProgramEntry} (actual : CSRResult w entry) (zero : entry.data.rd = 0) :
    limbs (Airbender.NativeMainDependencies.write w 2) = (0,0) := by rw [actual.written,if_pos zero]

theorem x12_oracle_preserved {w : Nat → F} {entry : CSRProgramEntry} (actual : CSRResult w entry) (rd : entry.data.rd = 12) :
    limbs (Airbender.NativeMainDependencies.write w 2) = ((w 90).val,(w 91).val) := by
  rw [actual.written,rd,if_neg (by decide : (12 : BitVec 5) ≠ 0)]

theorem delegation_clear {w : Nat → F} {entry : CSRProgramEntry} (actual : CSRResult w entry) (key : entry.data.immediate.lo = 1991) :
    limbs (Airbender.NativeMainDependencies.write w 2) = (0,0) := actual.clear key

theorem nonzero_CSR_is_nondeterminism {w : Nat → F} {entry : CSRProgramEntry} (actual : CSRResult w entry)
    (nonzero : (limbs (Airbender.NativeMainDependencies.write w 2)).2 ≠ 0) : entry.data.immediate.lo = 1984 := by
  rcases actual.key with first | second
  · exact first
  · exact False.elim (nonzero (congrArg Prod.snd (actual.clear second)))

theorem actual_write_ABI (w : Nat → F) : limbs (Airbender.NativeMainDependencies.write w 2) = ((w 43).val,(w 44).val) :=
  Airbender.NativeControlCSRProofs.write_limbs w

theorem exact_delegation_flag : NativeRuntimeCSR.delegated 1991 = 1 := by decide +kernel

theorem nondeterminism_not_delegation : NativeRuntimeCSR.delegated 1984 = 0 := by decide +kernel

theorem multiple_masks_retained : Airbender.NativeWorkerSchedule.nextHigh 24 = 48 := by decide +kernel

private def publicCSR (key : BitVec 12) : Airbender.NativeCallerDecoder.Program :=
  ⟨0,0,.CSRReg (key,.Regidx 0,.Regidx 12,.CSRRW),Sum.inr (),0,0,12,⟨key.toNat,0⟩,129,1⟩

theorem nondeterminism_is_seed_source : SeedSource (publicCSR 1984) :=
  Or.inr ⟨⟨(),0,0,12,⟨1984,0⟩,129,1⟩,rfl,rfl⟩

theorem delegation_is_not_seed_source : ¬ SeedSource (publicCSR 1991) := by
  rintro (⟨data,source⟩ | ⟨data,source,key⟩)
  · have none : (none : Option (DecoderData UnifiedMode)) = some data := source
    cases none
  · change some (⟨(),0,0,12,⟨1991,0⟩,129,1⟩ : DecoderData CSRMode) = some data at source
    cases source
    exact (by decide : (1991 : Nat) ≠ 1984) key

section
variable {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
  {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
  {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
  (effect : Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs)
include effect

theorem every_actual_MAIN_CSR {row : Airbender.NativeMixedMemoryOrder.MainRow}
    (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs) {entry : CSRProgramEntry}
    (fields : csrDecoderFields entry.instruction = some entry.data) (query : row.decoderQuery = entry.query) :
    CSRResult row.assignment entry := effect.main row member entry fields query

theorem all_control_CSR_edges_on_same_path : ∃ path, History batch.main.proofs workers inputs path ∧
    (∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs, ∀ entry : CSRProgramEntry,
      csrDecoderFields entry.instruction = some entry.data → row.decoderQuery = entry.query → entry.data.rd = 12 →
      (Airbender.NativeMainDependencies.read row.assignment 2,Airbender.NativeMainDependencies.write row.assignment 2) ∈ path.zip path.tail) := by
  obtain ⟨path,history,_,controls⟩ := effect.origins
  exact ⟨path,history,controls⟩

theorem every_nonzero_worker_origin {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) (nonzero : (w 135).val ≠ 0) :
    Airbender.NativeControlCSR.Origin before publicSetup batch.main.proofs (read w 42) := effect.workers w member active nonzero

theorem prior_public_origins_retained : Airbender.NativeControlOrigin.Effects before publicSetup batch workers inputs := effect.prior

theorem old_history_retained : Airbender.NativeControlHistory.Effects batch workers inputs := effect.prior.prior

theorem old_position_retained : Airbender.NativeCallerPosition.Effects batch workers inputs := effect.prior.prior.prior

theorem old_counts_retained : Airbender.NativeCallerCount.Effects batch workers inputs := effect.prior.prior.prior.prior

theorem old_joint_retained : Airbender.NativeJointReplay.Effects batch workers inputs := effect.prior.prior.prior.prior.prior.prior
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
    Airbender.NativeControlCSR.Effects before publicSetup batch workers inputs :=
  Airbender.NativeControlCSRProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeControlCSR
