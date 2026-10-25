import GKRProtocol.CleanBindings
import GKRProtocol.CleanArithmeticNative.UnifiedCached
import Airbender.Review.Circuits.UnifiedReduced.Artifact

namespace Airbender.Compiler.CleanLinksNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 10)) :
    FlatOperation.constraints (Airbender.UnifiedReduced.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 10)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.UnifiedReduced.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment base data) (Airbender.UnifiedReduced.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.UnifiedReduced.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 10)) :
    FlatOperation.constraints (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 10)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment base data) (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.UnifiedCached
