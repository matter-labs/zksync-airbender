import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.AddSubUncached
import Airbender.Review.Circuits.AddSub.Artifact

namespace Airbender.Compiler.CleanLinksNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory :
    FlatOperation.constraints (Airbender.AddSub.importedConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.expressions := by rfl

theorem retained_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.AddSub.importedConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment base data) (Airbender.AddSub.importedConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.AddSub.importedConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.expressions
    (arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory :
    FlatOperation.constraints (Airbender.AddSub.clockConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.expressions := by rfl

theorem retained_clock_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.AddSub.clockConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment base data) (Airbender.AddSub.clockConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.AddSub.clockConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.expressions
    (clock_arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.AddSubUncached
