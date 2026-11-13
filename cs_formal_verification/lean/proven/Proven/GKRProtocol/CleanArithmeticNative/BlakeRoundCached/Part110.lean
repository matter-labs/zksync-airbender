module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part109
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

local instance generatedBatch110Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch110Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding187 :
    CleanIdealChecks.encode native.placement native.expression187 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 187 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding187 :
    NumericPolynomialChecks.encodeCombination native.witness187 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 187 [] := by kernel_rfl

theorem native.idealInputsBinding187 :
    CleanExpression.inputs native.expression187 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 187 [] := by kernel_rfl

theorem native.checked187 :
    equal (CleanExpression.polynomial native.placement native.expression187)
        (combination native.relations native.witness187) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression187 native.witness187
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 187 (by decide +kernel) native.idealCodeBinding187
    native.idealRelationsBinding native.idealWitnessBinding187

theorem native.preserved187 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression187).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression187 native.placement native.relations native.witness187
    native.checked187 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression188 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨667⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨667⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness188 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨278, by decide⟩)]

theorem native.idealCodeBinding188 :
    CleanIdealChecks.encode native.placement native.expression188 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 188 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding188 :
    NumericPolynomialChecks.encodeCombination native.witness188 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 188 [] := by kernel_rfl

theorem native.idealInputsBinding188 :
    CleanExpression.inputs native.expression188 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 188 [] := by kernel_rfl

theorem native.checked188 :
    equal (CleanExpression.polynomial native.placement native.expression188)
        (combination native.relations native.witness188) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression188 native.witness188
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 188 (by decide +kernel) native.idealCodeBinding188
    native.idealRelationsBinding native.idealWitnessBinding188

theorem native.preserved188 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression188).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression188 native.placement native.relations native.witness188
    native.checked188 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression189 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨670⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨670⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness189 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨279, by decide⟩)]

theorem native.idealCodeBinding189 :
    CleanIdealChecks.encode native.placement native.expression189 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 189 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding189 :
    NumericPolynomialChecks.encodeCombination native.witness189 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 189 [] := by kernel_rfl

theorem native.idealInputsBinding189 :
    CleanExpression.inputs native.expression189 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 189 [] := by kernel_rfl

theorem native.checked189 :
    equal (CleanExpression.polynomial native.placement native.expression189)
        (combination native.relations native.witness189) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression189 native.witness189
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 189 (by decide +kernel) native.idealCodeBinding189
    native.idealRelationsBinding native.idealWitnessBinding189

theorem native.preserved189 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression189).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression189 native.placement native.relations native.witness189
    native.checked189 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression190 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨673⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨673⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness190 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨280, by decide⟩)]

theorem native.idealCodeBinding190 :
    CleanIdealChecks.encode native.placement native.expression190 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 190 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding190 :
    NumericPolynomialChecks.encodeCombination native.witness190 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 190 [] := by kernel_rfl

theorem native.idealInputsBinding190 :
    CleanExpression.inputs native.expression190 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 190 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
