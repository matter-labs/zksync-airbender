module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part073
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

local instance generatedBatch74Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch74Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding92 :
    CleanExpression.inputs native.expression92 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 92 [] := by kernel_rfl

theorem native.checked92 :
    equal (CleanExpression.polynomial native.placement native.expression92)
        (combination native.relations native.witness92) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression92 native.witness92
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 92
    (by decide +kernel) native.idealCodeBinding92 native.idealRelationsBinding native.idealWitnessBinding92

theorem native.preserved92 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression92).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression92 native.placement native.relations native.witness92
    native.checked92 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression93 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨61⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨61⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness93 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨134, by decide⟩)]

theorem native.idealCodeBinding93 :
    CleanIdealChecks.encode native.placement native.expression93 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 93 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding93 :
    NumericPolynomialChecks.encodeCombination native.witness93 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 93 [] := by kernel_rfl

theorem native.idealInputsBinding93 :
    CleanExpression.inputs native.expression93 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 93 [] := by kernel_rfl

theorem native.checked93 :
    equal (CleanExpression.polynomial native.placement native.expression93)
        (combination native.relations native.witness93) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression93 native.witness93
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 93
    (by decide +kernel) native.idealCodeBinding93 native.idealRelationsBinding native.idealWitnessBinding93

theorem native.preserved93 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression93).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression93 native.placement native.relations native.witness93
    native.checked93 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression94 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨62⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨62⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness94 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨135, by decide⟩)]

theorem native.idealCodeBinding94 :
    CleanIdealChecks.encode native.placement native.expression94 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 94 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding94 :
    NumericPolynomialChecks.encodeCombination native.witness94 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 94 [] := by kernel_rfl

theorem native.idealInputsBinding94 :
    CleanExpression.inputs native.expression94 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 94 [] := by kernel_rfl

theorem native.checked94 :
    equal (CleanExpression.polynomial native.placement native.expression94)
        (combination native.relations native.witness94) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression94 native.witness94
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 94
    (by decide +kernel) native.idealCodeBinding94 native.idealRelationsBinding native.idealWitnessBinding94

theorem native.preserved94 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression94).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression94 native.placement native.relations native.witness94
    native.checked94 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression95 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨63⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨63⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness95 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨136, by decide⟩)]

theorem native.idealCodeBinding95 :
    CleanIdealChecks.encode native.placement native.expression95 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 95 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding95 :
    NumericPolynomialChecks.encodeCombination native.witness95 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 95 [] := by kernel_rfl

theorem native.idealInputsBinding95 :
    CleanExpression.inputs native.expression95 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 95 [] := by kernel_rfl

theorem native.checked95 :
    equal (CleanExpression.polynomial native.placement native.expression95)
        (combination native.relations native.witness95) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression95 native.witness95
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 95
    (by decide +kernel) native.idealCodeBinding95 native.idealRelationsBinding native.idealWitnessBinding95

theorem native.preserved95 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression95).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression95 native.placement native.relations native.witness95
    native.checked95 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
