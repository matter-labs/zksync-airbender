import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivUncached
import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.Compiler.CleanLinksNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory :
    FlatOperation.constraints (Airbender.MulDiv.importedConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.expressions := by rfl

theorem retained_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.MulDiv.importedConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment base data) (Airbender.MulDiv.importedConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.MulDiv.importedConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.expressions
    (arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory :
    FlatOperation.constraints (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.expressions := by rfl

theorem retained_clock_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.MulDiv.clockConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment base data) (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.expressions
    (clock_arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.MulDivUncached
