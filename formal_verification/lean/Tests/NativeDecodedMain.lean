import Airbender.Review.Trace.Families.ReducedMachine.DecodedMainTheorems
import Tests.NativeCSRPositive
import Tests.NativeRuntimeQueryTransport

namespace Airbender.Tests.NativeDecodedMain
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.NativeDecodedMain
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def csrEntry : Airbender.NativeCallerDecoder.Program :=
  Airbender.Tests.NativeCSRPositive.entry.mapFamily Sum.inr

private theorem actual_query (active : Bool) :
    decoderQuery (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment = csrEntry.query := by
  cases active <;> decide +kernel

/-- Reuses the complete LOCAL native BODY, retaining execute0 and execute1. -/
theorem full_csr_body (active : Bool) : FlatOperation.ConstraintsHoldFlat
    (environment (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment)
    (importedConstraints NativeRuntimePool.table) :=
  Airbender.ReducedMachine.NativeCSRPositiveWitness.body active

theorem csr_tag_retained (active : Bool) :
    (lookupSelectors (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment)[0] = 25 := by
  cases active <;> decide +kernel

/-- Neither full local CSR row may borrow the ordinary decoded domain. -/
theorem csr_not_ordinary (active : Bool) : ¬ ∃ entry : UnifiedProgramEntry,
    unifiedDecoderFields entry.instruction = some entry.data ∧
    decoderQuery (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment = entry.query := by
  rintro ⟨entry,fields,query⟩
  exact Airbender.NativeDecodedQueryDomainProofs.unified (full_csr_body active) fields query 0 (csr_tag_retained active)

/-- The CSR branch derives its own local rule without fixture transfer. -/
theorem csr_write_rule (active : Bool) : RowWriteRule (Airbender.Tests.NativeCSRPositive.nativeRow active) := by
  apply native_decoded_main_write_rule _ (full_csr_body active) (entry := csrEntry)
  · rfl
  · exact actual_query active
  · cases active <;> decide +kernel

theorem inactive_request_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeCSRPositive.inactive_body_still_requests.2

theorem unrestricted_transfer_still_false : ¬ (∀ query : Vector F 4,
    NativeRuntimePool.table.Contains #[] query → NativeFixed.table.Contains #[] query) :=
  Airbender.Tests.NativeRuntimeQueryTransport.no_unrestricted_transfer

/-- Exact data columns survive the six-query bridge; no answer is supplied. -/
theorem both_constant_queries {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    NativeFixed.table.Contains #[] #v[w 36,w 56,w 57,16] ∧
      NativeFixed.table.Contains #[] #v[w 48,w 59,w 60,16] := by
  have actual := Airbender.NativeDecodedQueryDomainProofs.fixed_queries holds fields query
  exact ⟨actual.1,actual.2.1⟩

theorem all_dynamic_queries {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    ∀ slot : Fin 4, NativeFixed.table.Contains #[]
      #v[w (100 + 4 * slot.val),w (101 + 4 * slot.val),w (102 + 4 * slot.val),w (103 + 4 * slot.val)] :=
  (Airbender.NativeDecodedQueryDomainProofs.fixed_queries holds fields query).2.2

/-- Original public decoding, not a per-row mask/profile answer, supplies BODY. -/
theorem original_public_body {w : Nat → F} {setup : SparseDecoderSetup UnifiedMode}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    (∀ slot : Fin 4, (lookupSelectors w)[slot] ≠ 25) ∧
      FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table) :=
  native_public_ordinary_body image holds member

/-- Full conditional counted source, preserving the old named logical boundary. -/
theorem complete_counted_rules {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) : Effects batch :=
  native_counted_main_write_rules publicSetup embed memory ch pc gamma decoder config accepted image lookups
end Airbender.Tests.NativeDecodedMain
