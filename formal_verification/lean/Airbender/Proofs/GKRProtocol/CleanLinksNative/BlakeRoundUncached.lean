import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeRoundUncached
import Airbender.Review.Circuits.Blake2Round.Artifact

namespace Airbender.Compiler.CleanLinksNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem arithmetic_inventory (setup : Table Source.BaseField (fields 6)) :
    FlatOperation.constraints (Airbender.Blake2Round.importedConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.expressions := by rfl

theorem retained_constraints (setup : Table Source.BaseField (fields 6)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.Blake2Round.importedConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment base data) (Airbender.Blake2Round.importedConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.Blake2Round.importedConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.expressions
    (arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.arithmetic_preserved base data arithmetic) primitives

theorem clock_arithmetic_inventory (setup : Table Source.BaseField (fields 6)) :
    FlatOperation.constraints (Airbender.Blake2Round.clockConstraints (p := babyBearModulus) setup) = Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.expressions := by rfl

theorem retained_clock_constraints (setup : Table Source.BaseField (fields 6)) (base : GKRAddress → Source.BaseField)
    (data : ProverData Source.BaseField)
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.gates, gate.expressionResidual (base ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address) = 0)
    (primitives : ∀ lookup ∈ FlatOperation.lookups (Airbender.Blake2Round.clockConstraints (p := babyBearModulus) setup), lookup.Contains (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment base data)) :
    FlatOperation.ConstraintsHoldFlat (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment base data) (Airbender.Blake2Round.clockConstraints (p := babyBearModulus) setup) :=
  CleanExpression.retained_constraints (Airbender.Blake2Round.clockConstraints (p := babyBearModulus) setup) Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.expressions
    (clock_arithmetic_inventory setup ) (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.environment base data)
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.arithmetic_preserved base data arithmetic) primitives

end Airbender.Compiler.CleanLinksNative.BlakeRoundUncached
