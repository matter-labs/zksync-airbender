module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part107
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch108Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch108Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding180 :
    NumericPolynomialChecks.encodeCombination native.witness180 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 180 [] := by kernel_rfl

theorem native.idealInputsBinding180 :
    CleanExpression.inputs native.expression180 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 180 [] := by kernel_rfl

theorem native.checked180 :
    equal (CleanExpression.polynomial native.placement native.expression180)
        (combination native.relations native.witness180) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression180 native.witness180
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 180 (by decide +kernel) native.idealCodeBinding180
    native.idealRelationsBinding native.idealWitnessBinding180

theorem native.preserved180 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression180).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression180 native.placement native.relations native.witness180
    native.checked180 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression181 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨646⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨646⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness181 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨271, by decide⟩)]

theorem native.idealCodeBinding181 :
    CleanIdealChecks.encode native.placement native.expression181 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 181 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding181 :
    NumericPolynomialChecks.encodeCombination native.witness181 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 181 [] := by kernel_rfl

theorem native.idealInputsBinding181 :
    CleanExpression.inputs native.expression181 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 181 [] := by kernel_rfl

theorem native.checked181 :
    equal (CleanExpression.polynomial native.placement native.expression181)
        (combination native.relations native.witness181) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression181 native.witness181
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 181 (by decide +kernel) native.idealCodeBinding181
    native.idealRelationsBinding native.idealWitnessBinding181

theorem native.preserved181 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression181).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression181 native.placement native.relations native.witness181
    native.checked181 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression182 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨649⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨649⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness182 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨272, by decide⟩)]

theorem native.idealCodeBinding182 :
    CleanIdealChecks.encode native.placement native.expression182 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 182 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding182 :
    NumericPolynomialChecks.encodeCombination native.witness182 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 182 [] := by kernel_rfl

theorem native.idealInputsBinding182 :
    CleanExpression.inputs native.expression182 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 182 [] := by kernel_rfl

theorem native.checked182 :
    equal (CleanExpression.polynomial native.placement native.expression182)
        (combination native.relations native.witness182) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression182 native.witness182
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 182 (by decide +kernel) native.idealCodeBinding182
    native.idealRelationsBinding native.idealWitnessBinding182

theorem native.preserved182 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression182).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression182 native.placement native.relations native.witness182
    native.checked182 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression183 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨652⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨652⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness183 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨273, by decide⟩)]

theorem native.idealCodeBinding183 :
    CleanIdealChecks.encode native.placement native.expression183 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 183 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding183 :
    NumericPolynomialChecks.encodeCombination native.witness183 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 183 [] := by kernel_rfl

theorem native.idealInputsBinding183 :
    CleanExpression.inputs native.expression183 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 183 [] := by kernel_rfl

theorem native.checked183 :
    equal (CleanExpression.polynomial native.placement native.expression183)
        (combination native.relations native.witness183) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression183 native.witness183
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 183 (by decide +kernel) native.idealCodeBinding183
    native.idealRelationsBinding native.idealWitnessBinding183
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
