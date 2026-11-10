import Airbender.Proofs.GKRProtocol.CounterFrameChecks.SubwordMemoryCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.SubwordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 62 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns = [16, 14, 15] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots ∧
  (∀ index, 62 ≤ (Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 62 Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns [16, 14, 15] Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.source
    (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.SubwordMemoryCached
