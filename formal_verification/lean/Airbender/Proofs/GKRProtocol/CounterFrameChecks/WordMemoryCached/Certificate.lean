import Airbender.Proofs.GKRProtocol.CounterFrameChecks.WordMemoryCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 46 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns = [10, 8, 9] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots ∧
  (∀ index, 46 ≤ (Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.WordMemoryCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 46 Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns [10, 8, 9] Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.source
    (Airbender.Compiler.HelperNative.WordMemoryCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.WordMemoryCached
