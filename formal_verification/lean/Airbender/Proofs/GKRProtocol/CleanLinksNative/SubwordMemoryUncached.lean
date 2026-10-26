import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.SubwordMemoryUncached
import Airbender.Review.Circuits.SubwordMemory.Artifact

namespace Airbender.Compiler.CleanLinksNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment base data) (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.SubwordMemory.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment base data) (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.SubwordMemory.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.SubwordMemoryUncached
