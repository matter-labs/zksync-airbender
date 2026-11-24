module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part079
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch80Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch80Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness113 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨154, by decide⟩)]

theorem native.idealCodeBinding113 :
    CleanIdealChecks.encode native.placement native.expression113 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 113 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding113 :
    NumericPolynomialChecks.encodeCombination native.witness113 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 113 [] := by kernel_rfl

theorem native.idealInputsBinding113 :
    CleanExpression.inputs native.expression113 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 113 [] := by kernel_rfl

theorem native.checked113 :
    equal (CleanExpression.polynomial native.placement native.expression113)
        (combination native.relations native.witness113) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression113 native.witness113
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    113 (by decide +kernel) native.idealCodeBinding113 native.idealRelationsBinding native.idealWitnessBinding113

theorem native.preserved113 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression113).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression113 native.placement native.relations native.witness113
    native.checked113 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression114 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨98⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨98⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness114 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨155, by decide⟩)]

theorem native.idealCodeBinding114 :
    CleanIdealChecks.encode native.placement native.expression114 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 114 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding114 :
    NumericPolynomialChecks.encodeCombination native.witness114 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 114 [] := by kernel_rfl

theorem native.idealInputsBinding114 :
    CleanExpression.inputs native.expression114 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 114 [] := by kernel_rfl

theorem native.checked114 :
    equal (CleanExpression.polynomial native.placement native.expression114)
        (combination native.relations native.witness114) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression114 native.witness114
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    114 (by decide +kernel) native.idealCodeBinding114 native.idealRelationsBinding native.idealWitnessBinding114

theorem native.preserved114 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression114).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression114 native.placement native.relations native.witness114
    native.checked114 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression115 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨212⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨212⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness115 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨156, by decide⟩)]

theorem native.idealCodeBinding115 :
    CleanIdealChecks.encode native.placement native.expression115 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 115 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding115 :
    NumericPolynomialChecks.encodeCombination native.witness115 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 115 [] := by kernel_rfl

theorem native.idealInputsBinding115 :
    CleanExpression.inputs native.expression115 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 115 [] := by kernel_rfl

theorem native.checked115 :
    equal (CleanExpression.polynomial native.placement native.expression115)
        (combination native.relations native.witness115) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression115 native.witness115
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    115 (by decide +kernel) native.idealCodeBinding115 native.idealRelationsBinding native.idealWitnessBinding115

theorem native.preserved115 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression115).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression115 native.placement native.relations native.witness115
    native.checked115 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression116 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨218⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨218⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness116 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨157, by decide⟩)]

theorem native.idealCodeBinding116 :
    CleanIdealChecks.encode native.placement native.expression116 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 116 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding116 :
    NumericPolynomialChecks.encodeCombination native.witness116 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 116 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
