import GKRProtocol.CleanBindings
import GKRProtocol.CleanArithmeticNative.SubwordMemoryCached
import Airbender.Review.Circuits.SubwordMemory.Artifact

namespace Airbender.Compiler.CleanLinksNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment base data) (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment base data) (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.SubwordMemoryCached
