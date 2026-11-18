module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
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

local instance generatedBatch114Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch114Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression201 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨706⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨706⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness201 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨291, by decide⟩)]

theorem native.idealCodeBinding201 :
    CleanIdealChecks.encode native.placement native.expression201 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 201 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding201 :
    NumericPolynomialChecks.encodeCombination native.witness201 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 201 [] := by kernel_rfl

theorem native.idealInputsBinding201 :
    CleanExpression.inputs native.expression201 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 201 [] := by kernel_rfl

theorem native.checked201 :
    equal (CleanExpression.polynomial native.placement native.expression201)
        (combination native.relations native.witness201) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression201 native.witness201
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 201 (by decide +kernel) native.idealCodeBinding201
    native.idealRelationsBinding native.idealWitnessBinding201

theorem native.preserved201 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression201).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression201 native.placement native.relations native.witness201
    native.checked201 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression202 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨709⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨709⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness202 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨292, by decide⟩)]

theorem native.idealCodeBinding202 :
    CleanIdealChecks.encode native.placement native.expression202 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 202 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding202 :
    NumericPolynomialChecks.encodeCombination native.witness202 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 202 [] := by kernel_rfl

theorem native.idealInputsBinding202 :
    CleanExpression.inputs native.expression202 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 202 [] := by kernel_rfl

theorem native.checked202 :
    equal (CleanExpression.polynomial native.placement native.expression202)
        (combination native.relations native.witness202) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression202 native.witness202
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 202 (by decide +kernel) native.idealCodeBinding202
    native.idealRelationsBinding native.idealWitnessBinding202

theorem native.preserved202 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression202).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression202 native.placement native.relations native.witness202
    native.checked202 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression203 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨712⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨712⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness203 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨293, by decide⟩)]

theorem native.idealCodeBinding203 :
    CleanIdealChecks.encode native.placement native.expression203 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 203 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding203 :
    NumericPolynomialChecks.encodeCombination native.witness203 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 203 [] := by kernel_rfl

theorem native.idealInputsBinding203 :
    CleanExpression.inputs native.expression203 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 203 [] := by kernel_rfl

theorem native.checked203 :
    equal (CleanExpression.polynomial native.placement native.expression203)
        (combination native.relations native.witness203) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression203 native.witness203
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 203 (by decide +kernel) native.idealCodeBinding203
    native.idealRelationsBinding native.idealWitnessBinding203

theorem native.preserved203 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression203).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression203 native.placement native.relations native.witness203
    native.checked203 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression204 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨715⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨715⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness204 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨294, by decide⟩)]

theorem native.idealCodeBinding204 :
    CleanIdealChecks.encode native.placement native.expression204 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 204 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
