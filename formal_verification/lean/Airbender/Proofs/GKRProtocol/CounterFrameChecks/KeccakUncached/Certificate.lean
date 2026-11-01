import Airbender.Proofs.GKRProtocol.CounterFrameChecks.KeccakUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.KeccakUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 222 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns = [174, 173] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots ∧
  (∀ index, 222 ≤ (Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.KeccakUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 222 Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns [174, 173] Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.KeccakUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.KeccakUncached
