import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeRoundUncached.Bindings

namespace Airbender.Compiler.CounterFrameChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericCounterFrameChecks.check 632 data = true := by decide +kernel

theorem originalChecked :
  Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns = [537, 536] ∧ Function.Injective Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots ∧
  (∀ index, 632 ≤ (Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots index).val) ∧
  (∀ index, Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank.address (Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots index) =
    GKRAddress.BaseLayerWitness (Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns.get index)) ∧
  Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.source.all (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots)) = true ∧
  (Airbender.Compiler.HelperNative.BlakeRoundUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement)).all
    (erasureUntouched (List.ofFn Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots)) = true :=
  NumericCounterFrameChecks.check_sound data 632 Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns [537, 536] Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots
    Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.source
    (Airbender.Compiler.HelperNative.BlakeRoundUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement)) source_binding checked

end Airbender.Compiler.CounterFrameChecks.BlakeRoundUncached
