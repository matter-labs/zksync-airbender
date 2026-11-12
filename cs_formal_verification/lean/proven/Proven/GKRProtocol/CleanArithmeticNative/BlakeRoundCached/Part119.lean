module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part035
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part036
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part037
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part038
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part118
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

local instance generatedBatch119Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch119Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness218 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨308, by decide⟩)]

theorem native.idealCodeBinding218 :
    CleanIdealChecks.encode native.placement native.expression218 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 218 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding218 :
    NumericPolynomialChecks.encodeCombination native.witness218 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 218 [] := by kernel_rfl

theorem native.idealInputsBinding218 :
    CleanExpression.inputs native.expression218 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 218 [] := by kernel_rfl

theorem native.checked218 :
    equal (CleanExpression.polynomial native.placement native.expression218)
        (combination native.relations native.witness218) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression218 native.witness218
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 218 (by decide +kernel) native.idealCodeBinding218
    native.idealRelationsBinding native.idealWitnessBinding218

theorem native.preserved218 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression218).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression218 native.placement native.relations native.witness218
    native.checked218 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression219 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨760⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨760⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness219 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨309, by decide⟩)]

theorem native.idealCodeBinding219 :
    CleanIdealChecks.encode native.placement native.expression219 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 219 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding219 :
    NumericPolynomialChecks.encodeCombination native.witness219 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 219 [] := by kernel_rfl

theorem native.idealInputsBinding219 :
    CleanExpression.inputs native.expression219 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 219 [] := by kernel_rfl

theorem native.checked219 :
    equal (CleanExpression.polynomial native.placement native.expression219)
        (combination native.relations native.witness219) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression219 native.witness219
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 219 (by decide +kernel) native.idealCodeBinding219
    native.idealRelationsBinding native.idealWitnessBinding219

theorem native.preserved219 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression219).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression219 native.placement native.relations native.witness219
    native.checked219 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expressionsChunk0 : List (Airbender.Expression Source.BaseField) :=
  [native.expression0, native.expression1, native.expression2, native.expression3, native.expression4,
    native.expression5, native.expression6, native.expression7, native.expression8, native.expression9,
    native.expression10, native.expression11, native.expression12, native.expression13, native.expression14,
    native.expression15]

theorem native.scope0 :
    (CleanExpression.inputs native.expression0).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression0 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 0 (by decide +kernel) native.idealInputsBinding0

theorem native.scope1 :
    (CleanExpression.inputs native.expression1).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression1 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 1 (by decide +kernel) native.idealInputsBinding1

theorem native.scope2 :
    (CleanExpression.inputs native.expression2).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression2 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 2 (by decide +kernel) native.idealInputsBinding2

theorem native.scope3 :
    (CleanExpression.inputs native.expression3).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression3 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 3 (by decide +kernel) native.idealInputsBinding3

theorem native.scope4 :
    (CleanExpression.inputs native.expression4).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression4 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 4 (by decide +kernel) native.idealInputsBinding4

theorem native.scope5 :
    (CleanExpression.inputs native.expression5).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression5 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 5 (by decide +kernel) native.idealInputsBinding5

theorem native.scope6 :
    (CleanExpression.inputs native.expression6).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression6 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 6 (by decide +kernel) native.idealInputsBinding6

theorem native.scope7 :
    (CleanExpression.inputs native.expression7).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression7 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 7 (by decide +kernel) native.idealInputsBinding7

theorem native.scope8 :
    (CleanExpression.inputs native.expression8).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression8 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 8 (by decide +kernel) native.idealInputsBinding8

theorem native.scope9 :
    (CleanExpression.inputs native.expression9).all (fun index => decide (index < 763)) = true :=
  CleanIdealChecks.scope_at native.expression9 Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 9 (by decide +kernel) native.idealInputsBinding9
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
