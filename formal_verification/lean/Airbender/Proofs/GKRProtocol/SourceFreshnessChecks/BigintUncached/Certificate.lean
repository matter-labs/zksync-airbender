import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BigintUncached.Bindings

namespace Airbender.Compiler.SourceFreshnessChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericSourceFreshnessChecks.check data targetData = true := by decide +kernel

theorem originalChecked : targetAddresses.all (fun target => sourceAddresses.all (fun address => !addressEqual address target)) = true :=
  NumericSourceFreshnessChecks.check_sound sourceAddresses targetAddresses data targetData source_binding target_binding checked

theorem genericFresh : (List.range 216).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank.address (Airbender.Compiler.LookupNative.BigintUncached.native.sourcePlacement index)) (.BaseLayerWitness 159)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨0, by decide +kernel⟩) (List.get_mem targetAddresses ⟨0, by decide +kernel⟩)
  have target : targetAddresses.get ⟨0, by decide +kernel⟩ = .BaseLayerWitness 159 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

theorem range16Fresh : (List.range 216).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank.address (Airbender.Compiler.LookupNative.BigintUncached.native.sourcePlacement index)) (.BaseLayerWitness 157)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨1, by decide +kernel⟩) (List.get_mem targetAddresses ⟨1, by decide +kernel⟩)
  have target : targetAddresses.get ⟨1, by decide +kernel⟩ = .BaseLayerWitness 157 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

theorem timestampFresh : (List.range 216).all (fun index => !addressEqual (Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank.address (Airbender.Compiler.LookupNative.BigintUncached.native.sourcePlacement index)) (.BaseLayerWitness 158)) = true := by
  have item := List.all_eq_true.mp originalChecked
    (targetAddresses.get ⟨2, by decide +kernel⟩) (List.get_mem targetAddresses ⟨2, by decide +kernel⟩)
  have target : targetAddresses.get ⟨2, by decide +kernel⟩ = .BaseLayerWitness 158 := by rfl
  rw [target] at item
  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item

end Airbender.Compiler.SourceFreshnessChecks.BigintUncached
