import Airbender.Review.Trace.Families.ReducedMachine.CallerMixedQueriesTheorems
import Tests.NativeDelegationKeyAccounting

namespace Airbender.Tests.NativeCallerMixedQueries
open Airbender.NativeCallerRequests (F)
open Airbender.NativeCallerMixedQueries Airbender.ReducedMachine.Native Airbender.Verification Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure mixed payload only; NOT a full BODY or accepted native witness. Its
    second tuple retains a nonzero output at tag0, so the first tuple alone
    cannot certify the four-query relation. -/
private def mixed (n : Nat) : F :=
  if n = 9 then 1984 else if n = 22 ∨ n = 24 ∨ n = 64 then 1 else if n = 65 then -1 else 0

private def shifted (n : Nat) : F := if n = 29 then 1 else 0

theorem mixed_first_payload : (normalized mixed)[0] = #v[1984,1,0,25] := by decide +kernel

theorem mixed_second_payload : (normalized mixed)[1] = #v[0,0,-1,0] := by decide +kernel

theorem mixed_third_payload : (normalized mixed)[2] = #v[0,0,0,0] := by decide +kernel

theorem mixed_fourth_payload : (normalized mixed)[3] = #v[0,0,0,0] := by decide +kernel

theorem mixed_raw_flag_nonboolean : mixed 65 ≠ 0 ∧ mixed 65 ≠ 1 := by decide +kernel

theorem shift_last_tags : (normalized shifted)[2][3] = 37 ∧ (normalized shifted)[3][3] = 20 := by decide +kernel

theorem complete_local_body (active : Bool) : RuntimeRowEffects (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) :=
  Airbender.NativeCallerMixedQueryProofs.runtime (Airbender.ReducedMachine.NativeCSRPositiveWitness.body active)

theorem local_first_tuple (active : Bool) :
    (normalized (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))[0] = #v[1991,1,1,25] := by
  cases active <;> decide +kernel

theorem local_other_tuples (active : Bool) :
    ∀ slot : Fin 3, (normalized (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))[slot.val+1] = #v[0,0,0,0] := by
  intro slot
  fin_cases slot <;> cases active <;> decide +kernel

theorem local_all_exact (active : Bool) (slot : Fin 4) :
    query (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active) slot =
      (normalized (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))[slot] :=
  (complete_local_body active).queries.exact slot

theorem local_all_membership (active : Bool) (slot : Fin 4) :
    (Airbender.ReducedMachine.NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
      (normalized (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active))[slot] :=
  (complete_local_body active).membership slot

section
variable {w : Nat → F} (effect : RowEffects w)
include effect

theorem all_query_inputs_retained (slot : Fin 4) : query w slot = (normalized w)[slot] := effect.exact slot

theorem present_second_is_mixed (present : (csrRequest w).multiplicity ≠ 0) :
    w 101 = w 22 * w 58 + w 23 + 1 + w 25 + w 27 + w 29 + w 31 := effect.presentSecond present

theorem present_third_is_mixed (present : (csrRequest w).multiplicity ≠ 0) :
    w 102 = w 22 + (w 23 + 1 + w 25 + w 27 + w 29 + w 31) * w 65 := effect.presentThird present

theorem last_selector_difference : w 111 - w 115 = 17 * w 29 := effect.lastTags
end

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeDelegationKeyAccounting.inactive_requests_retained

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
      Airbender.NativeCallerMixedQueries.Effects batch.main.proofs :=
  Airbender.NativeCallerMixedQueryProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeCallerMixedQueries
