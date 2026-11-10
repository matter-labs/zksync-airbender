import Airbender.Proofs.GKRProtocol.FullArithmeticNative.WordMemoryCachedNumericData

namespace Airbender.Compiler.FullArithmeticNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

open NumericPolynomialChecks
local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

numeric_data_binding numericGateInputs_binding :
  native.artifact.gates.map (fun gate => NumericPolynomialChecks.normalize babyBearModulus
    (encode (NumericArithmeticChecks.gateInput gate))) = numericGateInputs
numeric_data_binding numericGateOutputs_binding :
  native.artifact.gates.map (fun gate => NumericPolynomialChecks.normalize babyBearModulus
    (encode (NumericArithmeticChecks.gateOutput gate))) = numericGateOutputs
numeric_data_binding numericKeys_binding :
  (native.addresses.map AddressUniqueChecks.addressCode).insertionSort (fun a b => a ≤ b) = numericKeys

noncomputable def numericCapture : NumericArithmeticChecks.Capture 52 := {
  sourceRows := numericSource.tree
  normalizedSourceRows := numericNormalizedSource.tree
  lowerRows := numericLowered.tree
  computedRows := numericExtensionData.tree
  backwardRows := numericBackward.tree
  forwardRows := numericForward.tree
  gateInputs := numericGateInputs.tree
  gateOutputs := numericGateOutputs.tree
  sortedAddressKeys := numericKeys
}

theorem numericBindings : NumericArithmeticChecks.Bindings native.addresses native.artifact native.certificate numericCapture := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, numericKeys_binding⟩
  · exact numericSource_binding.trans numericSource.tree_binding.symm
  · exact (List.map_map (g := NumericPolynomialChecks.normalize babyBearModulus) (f := encode) (l := native.artifact.source)).symm.trans
      ((congrArg (List.map (NumericPolynomialChecks.normalize babyBearModulus)) numericSource_binding).trans
        (numericNormalizedSource_binding.trans numericNormalizedSource.tree_binding.symm))
  · exact numericLowered_binding.trans numericLowered.tree_binding.symm
  · intro wire; rfl
  · intro wire
    exact NumericArithmeticChecks.initial_extension (by decide) native.extensionData _
      numericExtensionData.tree_valid
      (numericExtensionData_binding.trans numericExtensionData.tree_binding.symm) wire
  · intro index
    exact (NumericArithmeticChecks.vector_getD native.backwardData encodeCombination _
      numericBackward.tree_valid
      (numericBackward_binding.trans numericBackward.tree_binding.symm) index []).symm
  · intro index
    exact (NumericArithmeticChecks.vector_getD native.forwardData encodeCombination _
      numericForward.tree_valid
      (numericForward_binding.trans numericForward.tree_binding.symm) index []).symm
  · exact (NumericArithmeticChecks.map_encode_normalize native.artifact.gates NumericArithmeticChecks.gateInput).trans
      (numericGateInputs_binding.trans numericGateInputs.tree_binding.symm)
  · exact (NumericArithmeticChecks.map_encode_normalize native.artifact.gates NumericArithmeticChecks.gateOutput).trans
      (numericGateOutputs_binding.trans numericGateOutputs.tree_binding.symm)


end Airbender.Compiler.FullArithmeticNative.WordMemoryCached
