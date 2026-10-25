import GKRProtocol.CleanBindings
import GKRProtocol.CleanArithmeticNative.BigintUncached
import Airbender.Review.Circuits.Bigint.Artifact

namespace Airbender.Compiler.CleanLinksNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 3)) :
    FlatOperation.constraints (Airbender.Bigint.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 3)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.Bigint.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment base data) (Airbender.Bigint.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.Bigint.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 3)) :
    FlatOperation.constraints (Airbender.Bigint.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 3)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.Bigint.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment base data) (Airbender.Bigint.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.Bigint.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.BigintUncached
