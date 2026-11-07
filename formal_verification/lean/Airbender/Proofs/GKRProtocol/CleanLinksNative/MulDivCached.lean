import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivCached
import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.Compiler.CleanLinksNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory :
    FlatOperation.constraints (Airbender.MulDiv.importedConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.expressions := by rfl

theorem retained_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.MulDiv.importedConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment base data) (Airbender.MulDiv.importedConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.MulDiv.importedConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.expressions
    (arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory :
    FlatOperation.constraints (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.expressions := by rfl

theorem retained_clock_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.MulDiv.clockConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment base data) (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.expressions
    (clock_arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.MulDivCached
