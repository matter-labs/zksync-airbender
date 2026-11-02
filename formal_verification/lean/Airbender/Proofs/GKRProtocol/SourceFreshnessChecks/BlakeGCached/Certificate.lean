import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericSourceFreshnessChecks.check data targetData = true := by decide +kernel

theorem originalChecked : targetAddresses.all (fun target => sourceAddresses.all (fun address => !addressEqual address target)) = true :=
  NumericSourceFreshnessChecks.check_sound sourceAddresses targetAddresses data targetData source_binding target_binding checked

theorem genericFresh : (List.range 83).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank.address (Airbender.Compiler.LookupNative.BlakeGCached.native.sourcePlacement index)) (.BaseLayerWitness 56)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨0, by decide +kernel⟩) (List.get_mem targetAddresses ⟨0, by decide +kernel⟩)
  have target : targetAddresses.get ⟨0, by decide +kernel⟩ = .BaseLayerWitness 56 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

theorem timestampFresh : (List.range 83).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank.address (Airbender.Compiler.LookupNative.BlakeGCached.native.sourcePlacement index)) (.BaseLayerWitness 55)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨1, by decide +kernel⟩) (List.get_mem targetAddresses ⟨1, by decide +kernel⟩)
  have target : targetAddresses.get ⟨1, by decide +kernel⟩ = .BaseLayerWitness 55 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

end Airbender.Compiler.SourceFreshnessChecks.BlakeGCached
