import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BigintCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 216 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns = [159, 157, 158] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.BigintCached.native.slots ∧
  (∀ index, 216 ≤ (Airbender.Compiler.CounterFrameNative.BigintCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.BigintCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BigintCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.BigintCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BigintCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 216 Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns [159, 157, 158] Airbender.Compiler.CounterFrameNative.BigintCached.native.slots
    Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.source
    (Airbender.Compiler.HelperNative.BigintCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.BigintCached
