module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part072
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

local instance generatedBatch73Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch73Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness89 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨130, by decide⟩)]

theorem native.idealCodeBinding89 :
    CleanIdealChecks.encode native.placement native.expression89 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 89 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding89 :
    NumericPolynomialChecks.encodeCombination native.witness89 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 89 [] := by kernel_rfl

theorem native.idealInputsBinding89 :
    CleanExpression.inputs native.expression89 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 89 [] := by kernel_rfl

theorem native.checked89 :
    equal (CleanExpression.polynomial native.placement native.expression89)
        (combination native.relations native.witness89) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression89 native.witness89
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 89
    (by decide +kernel) native.idealCodeBinding89 native.idealRelationsBinding native.idealWitnessBinding89

theorem native.preserved89 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression89).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression89 native.placement native.relations native.witness89
    native.checked89 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression90 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.var ⟨58⟩

noncomputable def native.witness90 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨131, by decide⟩)]

theorem native.idealCodeBinding90 :
    CleanIdealChecks.encode native.placement native.expression90 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 90 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding90 :
    NumericPolynomialChecks.encodeCombination native.witness90 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 90 [] := by kernel_rfl

theorem native.idealInputsBinding90 :
    CleanExpression.inputs native.expression90 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 90 [] := by kernel_rfl

theorem native.checked90 :
    equal (CleanExpression.polynomial native.placement native.expression90)
        (combination native.relations native.witness90) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression90 native.witness90
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 90
    (by decide +kernel) native.idealCodeBinding90 native.idealRelationsBinding native.idealWitnessBinding90

theorem native.preserved90 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression90).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression90 native.placement native.relations native.witness90
    native.checked90 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression91 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨59⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨59⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness91 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨132, by decide⟩)]

theorem native.idealCodeBinding91 :
    CleanIdealChecks.encode native.placement native.expression91 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 91 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding91 :
    NumericPolynomialChecks.encodeCombination native.witness91 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 91 [] := by kernel_rfl

theorem native.idealInputsBinding91 :
    CleanExpression.inputs native.expression91 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 91 [] := by kernel_rfl

theorem native.checked91 :
    equal (CleanExpression.polynomial native.placement native.expression91)
        (combination native.relations native.witness91) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression91 native.witness91
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 91
    (by decide +kernel) native.idealCodeBinding91 native.idealRelationsBinding native.idealWitnessBinding91

theorem native.preserved91 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression91).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression91 native.placement native.relations native.witness91
    native.checked91 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression92 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨60⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨60⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness92 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨133, by decide⟩)]

theorem native.idealCodeBinding92 :
    CleanIdealChecks.encode native.placement native.expression92 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 92 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding92 :
    NumericPolynomialChecks.encodeCombination native.witness92 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 92 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
