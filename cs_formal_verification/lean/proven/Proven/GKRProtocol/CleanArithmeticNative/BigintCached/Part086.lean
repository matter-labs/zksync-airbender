module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part014
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part015
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part016
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part017
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part085
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

local instance generatedBatch86Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch86Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked133 :
    equal (CleanExpression.polynomial native.placement native.expression133)
        (combination native.relations native.witness133) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression133 native.witness133
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    133 (by decide +kernel) native.idealCodeBinding133 native.idealRelationsBinding native.idealWitnessBinding133

theorem native.preserved133 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression133).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression133 native.placement native.relations native.witness133
    native.checked133 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression134 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨272⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨272⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness134 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨175, by decide⟩)]

theorem native.idealCodeBinding134 :
    CleanIdealChecks.encode native.placement native.expression134 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 134 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding134 :
    NumericPolynomialChecks.encodeCombination native.witness134 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 134 [] := by kernel_rfl

theorem native.idealInputsBinding134 :
    CleanExpression.inputs native.expression134 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 134 [] := by kernel_rfl

theorem native.checked134 :
    equal (CleanExpression.polynomial native.placement native.expression134)
        (combination native.relations native.witness134) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression134 native.witness134
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    134 (by decide +kernel) native.idealCodeBinding134 native.idealRelationsBinding native.idealWitnessBinding134

theorem native.preserved134 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression134).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression134 native.placement native.relations native.witness134
    native.checked134 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expressionsChunk0 : List (Airbender.Expression Source.BaseField) :=
  [native.expression0, native.expression1, native.expression2, native.expression3, native.expression4,
    native.expression5, native.expression6, native.expression7, native.expression8, native.expression9,
    native.expression10, native.expression11, native.expression12, native.expression13, native.expression14,
    native.expression15]

theorem native.scope0 :
    (CleanExpression.inputs native.expression0).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression0 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 0 (by decide +kernel) native.idealInputsBinding0

theorem native.scope1 :
    (CleanExpression.inputs native.expression1).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression1 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 1 (by decide +kernel) native.idealInputsBinding1

theorem native.scope2 :
    (CleanExpression.inputs native.expression2).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression2 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 2 (by decide +kernel) native.idealInputsBinding2

theorem native.scope3 :
    (CleanExpression.inputs native.expression3).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression3 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 3 (by decide +kernel) native.idealInputsBinding3

theorem native.scope4 :
    (CleanExpression.inputs native.expression4).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression4 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 4 (by decide +kernel) native.idealInputsBinding4

theorem native.scope5 :
    (CleanExpression.inputs native.expression5).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression5 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 5 (by decide +kernel) native.idealInputsBinding5

theorem native.scope6 :
    (CleanExpression.inputs native.expression6).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression6 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 6 (by decide +kernel) native.idealInputsBinding6

theorem native.scope7 :
    (CleanExpression.inputs native.expression7).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression7 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 7 (by decide +kernel) native.idealInputsBinding7

theorem native.scope8 :
    (CleanExpression.inputs native.expression8).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression8 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 8 (by decide +kernel) native.idealInputsBinding8

theorem native.scope9 :
    (CleanExpression.inputs native.expression9).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression9 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 9 (by decide +kernel) native.idealInputsBinding9

theorem native.scope10 :
    (CleanExpression.inputs native.expression10).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression10 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 10 (by decide +kernel) native.idealInputsBinding10

theorem native.scope11 :
    (CleanExpression.inputs native.expression11).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression11 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 11 (by decide +kernel) native.idealInputsBinding11

theorem native.scope12 :
    (CleanExpression.inputs native.expression12).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression12 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 12 (by decide +kernel) native.idealInputsBinding12

theorem native.scope13 :
    (CleanExpression.inputs native.expression13).all (fun index => decide (index < 276)) = true :=
  CleanIdealChecks.scope_at native.expression13 Airbender.Compiler.CleanIdealNative.BigintCached.capture
    Airbender.Compiler.CleanIdealNative.BigintCached.checked 13 (by decide +kernel) native.idealInputsBinding13
end Airbender.Compiler.CleanArithmeticNative.BigintCached
