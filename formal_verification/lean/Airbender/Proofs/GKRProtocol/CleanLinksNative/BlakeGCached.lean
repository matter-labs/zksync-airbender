import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeGCached
import Airbender.Review.Circuits.Blake2G.Artifact

namespace Airbender.Compiler.CleanLinksNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.Blake2G.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.Blake2G.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment base data) (Airbender.Blake2G.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.Blake2G.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 9)) :
    FlatOperation.constraints (Airbender.Blake2G.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 9)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.Blake2G.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment base data) (Airbender.Blake2G.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.Blake2G.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.BlakeGCached
