import Airbender.Proofs.GKRProtocol.CounterFrameChecks.SubwordMemoryUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 62 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns = [16, 14, 15] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots ∧
  (∀ index, 62 ≤ (Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 62 Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns [16, 14, 15] Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.SubwordMemoryUncached
