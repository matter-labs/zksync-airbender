import Airbender.Proofs.GKRProtocol.CounterFrameChecks.WordMemoryUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 46 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns = [10, 8, 9] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots ∧
  (∀ index, 46 ≤ (Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 46 Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns [10, 8, 9] Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.WordMemoryUncached
