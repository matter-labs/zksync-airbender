import GKRProtocol.MemoryNative.AddSubCached

namespace Tests.GKRMemorySource
open Airbender Airbender.Compiler
open Airbender.Compiler.MemoryNative.AddSubCached
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private noncomputable def original := (native.memoryReadRows[0]?).getD
  (Source.MemoryRow.mk (.constant 0) .zero .zero .zero)

theorem rejects_changed_source_address_space :
    native.memoryReadCertificate0.check {original with addressSpace := .constant 3}
      native.sourcePlacement native.bank native.raw0 = false := by decide +kernel

theorem rejects_changed_consumed_payload :
    native.memoryReadCertificate0.check original native.sourcePlacement native.bank
      (.add native.raw0 (.constant (.natural 1))) = false := by decide +kernel

theorem rejects_exchanged_timestamp_limbs :
    native.memoryReadCertificate0.check
      {original with timestamp := ⟨original.timestamp.high, original.timestamp.low⟩}
      native.sourcePlacement native.bank native.raw0 = false := by decide +kernel

theorem rejects_unexpanded_memory_cache_as_base_input :
    native.leaf0.inputs.all (fun address => ConsumerNative.AddSubCached.native.typing.compatible (address, .base)) = false := by
  decide +kernel

theorem rejects_lookup_alpha_in_memory_encoding :
    (LookupPayload.memoryExpression (MemorySymbolPlacement.forBank native.bank)
      (.constant (.lookupPower 0))).isSome = false := by decide +kernel

theorem keeps_gamma_separate_from_native_inputs :
    (MemorySymbolPlacement.forBank native.bank).gamma ≠
      (MemorySymbolPlacement.forBank native.bank).address (.BaseLayerWitness 0) := by decide +kernel

theorem rejects_dangling_original_variable :
    Source.MemoryField.referencesValid 42 3 0 false (.input (.Variable 42)) = false := by decide +kernel

theorem rejects_dangling_history_slot :
    Source.MemoryField.referencesValid 42 3 0 false (.readTimestamp 3 ⟨0, by decide⟩) = false := by decide +kernel

theorem rejects_replaced_execution_predicate :
    ({native.memoryReadMaskField with «source» := .constant 0} : MemoryFieldAgreement native.copyRelations).check
      native.sourcePlacement = false := by decide +kernel

private def history : Source.MemoryValues :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 9⟩

private def valueChallenge : CacheChallenges Source.BaseField :=
  ⟨0, 0, fun index => if index.val = 4 then 1 else 0⟩

/-- The RAM read channel consumes the final snapshot; the write channel inserts
the zero initialization. Their direction is observable in the data coordinate. -/
theorem keeps_initialization_and_teardown_directions :
    (((Source.initializationRequests 1 2 23)[0]?).map (fun rows =>
      (rows.1.fingerprint history (RingHom.id _) valueChallenge,
       rows.2.fingerprint history (RingHom.id _) valueChallenge))) = some (10, 1) := by decide +kernel

theorem permits_shared_native_primitive_with_exact_source_occurrences :
    (([0, 0] : List Nat).map (fun _ => (7 : Int))).prod = ([7, 7] : List Int).prod := by
  apply memory_product_translation (fun _ => (7 : Int)) [7, 7] (native := [0, 0]) (labels := [0, 1])
  · exact .cons rfl (.cons rfl .nil)
  · decide +kernel

end Tests.GKRMemorySource
