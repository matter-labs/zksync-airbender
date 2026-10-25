import GKRProtocol.CleanBindings
import GKRProtocol.CleanArithmeticNative.JumpBranchCached
import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.Compiler.CleanLinksNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory :
    FlatOperation.constraints (Airbender.JumpBranchSlt.importedConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.expressions := by rfl

theorem retained_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.JumpBranchSlt.importedConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment base data) (Airbender.JumpBranchSlt.importedConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.JumpBranchSlt.importedConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.expressions
    (arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory :
    FlatOperation.constraints (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) = Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.expressions := by rfl

theorem retained_clock_constraints (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment base data) (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) :=
  CleanExpression.retained_constraints (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.expressions
    (clock_arithmetic_inventory ) (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.JumpBranchCached
