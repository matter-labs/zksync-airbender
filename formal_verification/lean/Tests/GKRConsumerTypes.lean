import Airbender.Proofs.GKRProtocol.ConsumerNative.AddSubCached

namespace Tests.GKRConsumerTypes
open Airbender Airbender.Compiler
open Airbender.Compiler.ConsumerNative.AddSubCached
set_option warningAsError true
set_option maxRecDepth 32768

theorem accepts_actual_consumers : native.typing.check = true := native.checked

/-- An assertion gate has no output; port coverage alone cannot detect omission. -/
theorem assertion_has_no_outputs : native.node15.rawOutputs = [] := by decide +kernel

theorem rejects_omitted_assertion :
    ({ native.typing with nodes := native.typing.nodes.take 15 ++ native.typing.nodes.drop 16 } :
      ConsumerTyping).consumersValid = false := by decide +kernel

theorem rejects_changed_field_role :
    ({ native.typing with nodes :=
      { native.node0 with outputs := native.node0.outputs.map (fun port => (port.1, WireKind.extension)) } ::
        native.typing.nodes.drop 1 } : ConsumerTyping).check = false := by decide +kernel

theorem rejects_repeated_flattened_address :
    native.typing.nodeValid { native.node0 with distinctGroups :=
      [[GKRAddress.BaseLayerWitness 0, GKRAddress.BaseLayerWitness 0]] } = false := by decide +kernel

theorem rejects_changed_input_role :
    native.typing.nodeValid { native.node0 with
      inputs := native.node0.inputs.map (fun port => (port.1, WireKind.extension)) } = false := by decide +kernel

end Tests.GKRConsumerTypes
