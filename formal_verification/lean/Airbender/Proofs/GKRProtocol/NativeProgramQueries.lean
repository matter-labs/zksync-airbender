import Airbender.Review.Compiler.NativePublicSetup
import Airbender.Proofs.GKRProtocol.ProgramSetupNative
import Airbender.Proofs.GKRProtocol.ProgramSetupMembership

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

/-- Native exact matching can use this lemma after operand transport. -/
theorem tagged_decoder_member (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (layout : ProgramSetup.Layout)
    (selected : layouts configuration = some layout) (tagged : layout.tagged = true)
    (positive : 0 < layout.width - 1)
    (widths : ∀ row ∈ decoder configuration, row.length = layout.width - 1)
    (index : Nat) (payload : List Source.BaseField)
    (payloadWidth : payload.length = layout.width - 1)
    (same : ProgramSetup.packTagged layout.width 46 payload = rows decoder wordAt configuration 0 index)
    (active : payload.head? ≠ some (-1)) : payload ∈ decoder configuration := by
  apply ProgramSetup.tagged_decoder_query_member layout (retainedRows configuration 0)
    (decoder configuration) wordAt index tagged (by decide +kernel) (by decide +kernel)
    positive widths payload payloadWidth ?_ active
  simpa [rows, selected, ProgramSetup.groupRows] using same

theorem untagged_decoder_member (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (layout : ProgramSetup.Layout)
    (selected : layouts configuration = some layout) (untagged : layout.tagged = false)
    (positive : 0 < layout.width) (index : Nat) (payload : List Source.BaseField)
    (same : payload = rows decoder wordAt configuration 0 index)
    (active : payload.head? ≠ some (-1)) : payload ∈ decoder configuration := by
  apply ProgramSetup.untagged_decoder_query_member layout (retainedRows configuration 0)
    (decoder configuration) wordAt index untagged positive payload ?_ active
  simpa [rows, selected, ProgramSetup.groupRows] using same

/-- The ROM result contains the public word, with a bounded native word index. -/
theorem rom_member (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (layout : ProgramSetup.Layout)
    (selected : layouts configuration = some layout) (tagged : layout.tagged = true)
    (index : Nat) (payload : List Source.BaseField) (payloadWidth : payload.length = 3)
    (same : ProgramSetup.packTagged layout.width 34 payload = rows decoder wordAt configuration 0 index) :
    ∃ wordIndex, wordIndex < layout.romWords ∧ payload = ProgramSetup.romPayload wordAt wordIndex := by
  apply ProgramSetup.rom_query_payload layout (retainedRows configuration 0)
    (decoder configuration) wordAt index tagged (by decide +kernel) (by decide +kernel)
    payload payloadWidth
  simpa [rows, selected, ProgramSetup.groupRows] using same

/-- Queries for a fixed helper table retain their original native membership. -/
theorem fixed_member (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (layout : ProgramSetup.Layout)
    (selected : layouts configuration = some layout) (tagged : layout.tagged = true)
    (index : Nat) (query : List Source.BaseField)
    (same : query = rows decoder wordAt configuration 0 index)
    (nonzero : query.getLast?.getD 0 ≠ 0)
    (notDecoder : query.getLast?.getD 0 ≠ 46)
    (notROM : query.getLast?.getD 0 ≠ 34) : query = retainedRows configuration 0 index := by
  apply ProgramSetup.fixed_query_region layout (retainedRows configuration 0)
    (decoder configuration) wordAt index tagged query ?_ nonzero notDecoder notROM
  simpa [rows, selected, ProgramSetup.groupRows] using same

/-- A query outside the two program tags retains a fixed row or zero padding. -/
theorem fixed_or_zero_member (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration) (layout : ProgramSetup.Layout)
    (selected : layouts configuration = some layout) (tagged : layout.tagged = true)
    (index : Nat) (query : List Source.BaseField)
    (same : query = rows decoder wordAt configuration 0 index)
    (notDecoder : query.getLast?.getD 0 ≠ 46)
    (notROM : query.getLast?.getD 0 ≠ 34) :
    query = retainedRows configuration 0 index ∨ query = List.replicate layout.width 0 := by
  apply ProgramSetup.fixed_query_or_zero layout (retainedRows configuration 0)
    (decoder configuration) wordAt index tagged query ?_ notDecoder notROM
  simpa [rows, selected, ProgramSetup.groupRows] using same

end Airbender.Compiler.NativeProgramSetup
