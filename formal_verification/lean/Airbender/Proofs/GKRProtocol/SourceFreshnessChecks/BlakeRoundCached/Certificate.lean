import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeRoundCached.Bindings

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericSourceFreshnessChecks.check data targetData = true := by decide +kernel

theorem originalChecked : targetAddresses.all (fun target => sourceAddresses.all (fun address => !addressEqual address target)) = true :=
  NumericSourceFreshnessChecks.check_sound sourceAddresses targetAddresses data targetData source_binding target_binding checked

theorem genericFresh : (List.range 632).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundCached.native.sourcePlacement index)) (.BaseLayerWitness 537)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨0, by decide +kernel⟩) (List.get_mem targetAddresses ⟨0, by decide +kernel⟩)
  have target : targetAddresses.get ⟨0, by decide +kernel⟩ = .BaseLayerWitness 537 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

theorem timestampFresh : (List.range 632).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundCached.native.sourcePlacement index)) (.BaseLayerWitness 536)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨1, by decide +kernel⟩) (List.get_mem targetAddresses ⟨1, by decide +kernel⟩)
  have target : targetAddresses.get ⟨1, by decide +kernel⟩ = .BaseLayerWitness 536 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

end Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached
