import GKRProtocol.CleanBindings
import GKRProtocol.CleanArithmeticNative.WordMemoryCached
import Airbender.Review.Circuits.WordMemory.Artifact

namespace Airbender.Compiler.CleanLinksNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment base data) (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.WordMemory.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment base data) (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.WordMemory.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.WordMemoryCached
