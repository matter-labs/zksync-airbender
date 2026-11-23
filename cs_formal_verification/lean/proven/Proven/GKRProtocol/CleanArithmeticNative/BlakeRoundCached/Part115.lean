module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part114
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

local instance generatedBatch115Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch115Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding204 :
    NumericPolynomialChecks.encodeCombination native.witness204 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 204 [] := by kernel_rfl

theorem native.idealInputsBinding204 :
    CleanExpression.inputs native.expression204 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 204 [] := by kernel_rfl

theorem native.checked204 :
    equal (CleanExpression.polynomial native.placement native.expression204)
        (combination native.relations native.witness204) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression204 native.witness204
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 204 (by decide +kernel) native.idealCodeBinding204
    native.idealRelationsBinding native.idealWitnessBinding204

theorem native.preserved204 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression204).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression204 native.placement native.relations native.witness204
    native.checked204 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression205 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨718⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨718⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness205 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨295, by decide⟩)]

theorem native.idealCodeBinding205 :
    CleanIdealChecks.encode native.placement native.expression205 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 205 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding205 :
    NumericPolynomialChecks.encodeCombination native.witness205 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 205 [] := by kernel_rfl

theorem native.idealInputsBinding205 :
    CleanExpression.inputs native.expression205 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 205 [] := by kernel_rfl

theorem native.checked205 :
    equal (CleanExpression.polynomial native.placement native.expression205)
        (combination native.relations native.witness205) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression205 native.witness205
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 205 (by decide +kernel) native.idealCodeBinding205
    native.idealRelationsBinding native.idealWitnessBinding205

theorem native.preserved205 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression205).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression205 native.placement native.relations native.witness205
    native.checked205 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression206 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨721⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨721⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness206 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨296, by decide⟩)]

theorem native.idealCodeBinding206 :
    CleanIdealChecks.encode native.placement native.expression206 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 206 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding206 :
    NumericPolynomialChecks.encodeCombination native.witness206 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 206 [] := by kernel_rfl

theorem native.idealInputsBinding206 :
    CleanExpression.inputs native.expression206 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 206 [] := by kernel_rfl

theorem native.checked206 :
    equal (CleanExpression.polynomial native.placement native.expression206)
        (combination native.relations native.witness206) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression206 native.witness206
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 206 (by decide +kernel) native.idealCodeBinding206
    native.idealRelationsBinding native.idealWitnessBinding206

theorem native.preserved206 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression206).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression206 native.placement native.relations native.witness206
    native.checked206 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression207 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨724⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨724⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness207 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨297, by decide⟩)]

theorem native.idealCodeBinding207 :
    CleanIdealChecks.encode native.placement native.expression207 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 207 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding207 :
    NumericPolynomialChecks.encodeCombination native.witness207 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 207 [] := by kernel_rfl

theorem native.idealInputsBinding207 :
    CleanExpression.inputs native.expression207 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 207 [] := by kernel_rfl

theorem native.checked207 :
    equal (CleanExpression.polynomial native.placement native.expression207)
        (combination native.relations native.witness207) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression207 native.witness207
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 207 (by decide +kernel) native.idealCodeBinding207
    native.idealRelationsBinding native.idealWitnessBinding207
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
