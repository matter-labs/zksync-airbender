import Airbender.Proofs.GKRProtocol.Native.AddSubCached
import Airbender.Proofs.GKRProtocol.Native.JumpBranchCached
import Airbender.Proofs.GKRProtocol.Native.BigintCached

namespace Tests.GKRLookupFields
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private noncomputable def padding := LookupNative.JumpBranchCached.native.field0_2
private noncomputable def selector := LookupNative.JumpBranchCached.native.field0_9
private noncomputable def decoderMask := LookupNative.AddSubCached.native.field6_0
private noncomputable def originalRange := LookupNative.AddSubCached.native.field0_0
private noncomputable def scratchRange := LookupNative.BigintCached.native.field77_0

theorem actual_padding_field :
    (match padding.source with | .zero => true | _ => false) = true := by decide +kernel

theorem actual_table_selector :
    (match selector.source with | .table _ => true | _ => false) = true := by decide +kernel

theorem actual_scratch_source :
    (match scratchRange.source with | .input (.Variable 194) => true | _ => false) = true := by decide +kernel

private noncomputable def changedPadding :=
  { padding with lowered := Expression.add padding.lowered (.constant 1) }

theorem rejects_nonzero_padding :
    changedPadding.check LookupNative.JumpBranchCached.native.sourcePlacement = false := by decide +kernel

private noncomputable def changedSelector :=
  { selector with lowered := Expression.add selector.lowered (.constant 1) }

theorem rejects_changed_table_selector :
    changedSelector.check LookupNative.JumpBranchCached.native.sourcePlacement = false := by decide +kernel

private noncomputable def changedMask :=
  { decoderMask with lowered := Expression.add decoderMask.lowered (.constant 1) }

theorem rejects_changed_decoder_mask :
    changedMask.check LookupNative.AddSubCached.native.sourcePlacement = false := by decide +kernel

private noncomputable def changedScratch :=
  { scratchRange with lowered := Expression.atom (LookupNative.BigintCached.native.sourcePlacement 0) }

theorem rejects_wrong_scratch_binding :
    changedScratch.check LookupNative.BigintCached.native.sourcePlacement = false := by decide +kernel

private noncomputable def changedSource : LookupFieldAgreement LookupNative.AddSubCached.native.copyRelations :=
  ⟨.input (.Variable 38), originalRange.lowered, originalRange.witness⟩

theorem rejects_changed_authored_source :
    changedSource.check LookupNative.AddSubCached.native.sourcePlacement = false := by decide +kernel

theorem rejects_wrong_source_projection :
    originalRange.check (fun _ => LookupNative.AddSubCached.native.sourcePlacement 0) = false := by decide +kernel

end Tests.GKRLookupFields
