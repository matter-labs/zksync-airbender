import Airbender.Review.Trace.Families.ReducedMachine.CallerValidityTheorems
import Tests.NativeCallerMixedQueries

namespace Airbender.Tests.NativeCallerValidity
open Airbender.NativeCallerRequests (F)
open Airbender.NativeCallerValidity Airbender.ReducedMachine.Native Airbender.Verification Airbender.Trace
open Airbender.ReducedMachine
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Existing complete LOCAL fixtures only, not global accepted source witnesses. -/
theorem complete_local_body (active : Bool) : RowEffects (NativeCSRPositiveWitness.assignment active) :=
  Airbender.NativeCallerValidityProofs.body (NativeCSRPositiveWitness.body active)

theorem local_request_one (active : Bool) :
    csrRequest (NativeCSRPositiveWitness.assignment active) = ⟨1,1991,some 0,3⟩ := by
  cases active <;> decide +kernel

theorem local_competitors_zero (active : Bool) :
    competing (NativeCSRPositiveWitness.assignment active) = #v[0,0,0,0,0,0] := by
  cases active <;> decide +kernel

theorem inactive_validity : RowEffects (NativeCSRPositiveWitness.assignment false) := complete_local_body false

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeCallerMixedQueries.inactive_requests_retained

theorem actual_zero_tuple (q : Vector F 4) (member : NativeRuntimePool.table.Contains #[] q)
    (tag : q[3] = 0) : q = #v[0,0,0,0] := Airbender.NativeCallerValidityProofs.zero_tuple q member tag

theorem all_comparison_outputs_boolean (q : Vector F 4) (member : NativeRuntimePool.table.Contains #[] q)
    (tag : q[3] = 22) : q[2] = 0 ∨ q[2] = 1 :=
  Airbender.NativeCallerValidityProofs.comparison_boolean q member tag

section
variable {w : Nat → F} (effect : RowEffects w)
include effect

theorem individual_boolean : (csrRequest w).multiplicity = 0 ∨ (csrRequest w).multiplicity = 1 := effect.boolean

theorem complete_request_shape : csrRequest w = ⟨0,0,some 0,3⟩ ∨ csrRequest w = ⟨1,1991,some (w 36),3⟩ :=
  effect.request

theorem raw_key (present : (csrRequest w).multiplicity ≠ 0) : w 9 = 1991 := (effect.inputs present).1

theorem raw_delegate_one (present : (csrRequest w).multiplicity ≠ 0) : w 65 = 1 := (effect.inputs present).2.1

theorem abi_high_bound (present : (csrRequest w).multiplicity ≠ 0) : (w 36).val < 65536 := (effect.inputs present).2.2

theorem all_competitors_zero (present : (csrRequest w).multiplicity ≠ 0) : competing w = #v[0,0,0,0,0,0] :=
  effect.isolation present

theorem negative_weight_rejected (negative : (csrRequest w).multiplicity = -1) : False := by
  have bad : ¬ ((-1 : F) = 0 ∨ (-1 : F) = 1) := by decide +kernel
  exact bad (by simpa only [negative] using effect.boolean)

theorem wrong_raw_key_rejected (present : (csrRequest w).multiplicity ≠ 0) (wrong : w 9 ≠ 1991) : False :=
  wrong (effect.inputs present).1

theorem wide_abi_rejected (present : (csrRequest w).multiplicity ≠ 0) (wide : 65536 ≤ (w 36).val) : False := by
  have bound := (effect.inputs present).2.2
  omega

theorem full_mixed_memberships_retained (slot : Fin 4) :
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] (Airbender.NativeCallerMixedQueries.normalized w)[slot] :=
  effect.prior.membership slot
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
    Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs ∧
      Airbender.NativeCallerMixedQueries.Effects batch.main.proofs ∧
        Airbender.NativeCallerValidity.Effects batch.main.proofs :=
  Airbender.NativeCallerValidityProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeCallerValidity
