module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part102
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

local instance generatedBatch103Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch103Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding163 :
    CleanIdealChecks.encode native.placement native.expression163 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 163 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding163 :
    NumericPolynomialChecks.encodeCombination native.witness163 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 163 [] := by kernel_rfl

theorem native.idealInputsBinding163 :
    CleanExpression.inputs native.expression163 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 163 [] := by kernel_rfl

theorem native.checked163 :
    equal (CleanExpression.polynomial native.placement native.expression163)
        (combination native.relations native.witness163) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression163 native.witness163
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 163 (by decide +kernel) native.idealCodeBinding163
    native.idealRelationsBinding native.idealWitnessBinding163

theorem native.preserved163 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression163).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression163 native.placement native.relations native.witness163
    native.checked163 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression164 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨557⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨557⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness164 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨254, by decide⟩)]

theorem native.idealCodeBinding164 :
    CleanIdealChecks.encode native.placement native.expression164 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 164 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding164 :
    NumericPolynomialChecks.encodeCombination native.witness164 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 164 [] := by kernel_rfl

theorem native.idealInputsBinding164 :
    CleanExpression.inputs native.expression164 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 164 [] := by kernel_rfl

theorem native.checked164 :
    equal (CleanExpression.polynomial native.placement native.expression164)
        (combination native.relations native.witness164) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression164 native.witness164
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 164 (by decide +kernel) native.idealCodeBinding164
    native.idealRelationsBinding native.idealWitnessBinding164

theorem native.preserved164 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression164).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression164 native.placement native.relations native.witness164
    native.checked164 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression165 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨563⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨563⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness165 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨255, by decide⟩)]

theorem native.idealCodeBinding165 :
    CleanIdealChecks.encode native.placement native.expression165 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 165 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding165 :
    NumericPolynomialChecks.encodeCombination native.witness165 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 165 [] := by kernel_rfl

theorem native.idealInputsBinding165 :
    CleanExpression.inputs native.expression165 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 165 [] := by kernel_rfl

theorem native.checked165 :
    equal (CleanExpression.polynomial native.placement native.expression165)
        (combination native.relations native.witness165) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression165 native.witness165
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 165 (by decide +kernel) native.idealCodeBinding165
    native.idealRelationsBinding native.idealWitnessBinding165

theorem native.preserved165 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression165).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression165 native.placement native.relations native.witness165
    native.checked165 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression166 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨569⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨569⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness166 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨256, by decide⟩)]

theorem native.idealCodeBinding166 :
    CleanIdealChecks.encode native.placement native.expression166 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 166 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding166 :
    NumericPolynomialChecks.encodeCombination native.witness166 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 166 [] := by kernel_rfl

theorem native.idealInputsBinding166 :
    CleanExpression.inputs native.expression166 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 166 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
