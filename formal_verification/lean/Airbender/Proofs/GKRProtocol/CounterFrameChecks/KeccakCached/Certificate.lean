import Airbender.Proofs.GKRProtocol.CounterFrameChecks.KeccakCached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 222 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns = [174, 173] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots ∧
  (∀ index, 222 ≤ (Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.KeccakCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 222 Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns [174, 173] Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.source
    (Airbender.Compiler.HelperNative.KeccakCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.KeccakCached
