import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.ShiftBinopUncached
import Airbender.Review.Circuits.ShiftBinop.Artifact

namespace Airbender.Compiler.CleanLinksNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory :
    FlatOperation.constraints (Airbender.ShiftBinop.importedConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.expressions := by rfl

theorem retained_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.ShiftBinop.importedConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment base data) (Airbender.ShiftBinop.importedConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.ShiftBinop.importedConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.expressions
    (arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory :
    FlatOperation.constraints (Airbender.ShiftBinop.clockConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.expressions := by rfl

theorem retained_clock_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.ShiftBinop.clockConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment base data) (Airbender.ShiftBinop.clockConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.ShiftBinop.clockConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.expressions
    (clock_arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.ShiftBinopUncached
