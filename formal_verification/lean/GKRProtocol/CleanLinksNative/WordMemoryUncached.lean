import GKRProtocol.CleanBindings
import GKRProtocol.CleanArithmeticNative.WordMemoryUncached
import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.Compiler.CleanLinksNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment base data) (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment base data) (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.WordMemoryUncached
