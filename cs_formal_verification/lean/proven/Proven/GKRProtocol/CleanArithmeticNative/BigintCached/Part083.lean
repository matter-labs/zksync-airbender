module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part082
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

local instance generatedBatch83Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch83Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding123 :
    NumericPolynomialChecks.encodeCombination native.witness123 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 123 [] := by kernel_rfl

theorem native.idealInputsBinding123 :
    CleanExpression.inputs native.expression123 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 123 [] := by kernel_rfl

theorem native.checked123 :
    equal (CleanExpression.polynomial native.placement native.expression123)
        (combination native.relations native.witness123) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression123 native.witness123
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    123 (by decide +kernel) native.idealCodeBinding123 native.idealRelationsBinding native.idealWitnessBinding123

theorem native.preserved123 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression123).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression123 native.placement native.relations native.witness123
    native.checked123 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression124 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨242⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨242⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness124 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨165, by decide⟩)]

theorem native.idealCodeBinding124 :
    CleanIdealChecks.encode native.placement native.expression124 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 124 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding124 :
    NumericPolynomialChecks.encodeCombination native.witness124 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 124 [] := by kernel_rfl

theorem native.idealInputsBinding124 :
    CleanExpression.inputs native.expression124 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 124 [] := by kernel_rfl

theorem native.checked124 :
    equal (CleanExpression.polynomial native.placement native.expression124)
        (combination native.relations native.witness124) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression124 native.witness124
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    124 (by decide +kernel) native.idealCodeBinding124 native.idealRelationsBinding native.idealWitnessBinding124

theorem native.preserved124 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression124).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression124 native.placement native.relations native.witness124
    native.checked124 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression125 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨245⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨245⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness125 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨166, by decide⟩)]

theorem native.idealCodeBinding125 :
    CleanIdealChecks.encode native.placement native.expression125 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 125 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding125 :
    NumericPolynomialChecks.encodeCombination native.witness125 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 125 [] := by kernel_rfl

theorem native.idealInputsBinding125 :
    CleanExpression.inputs native.expression125 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 125 [] := by kernel_rfl

theorem native.checked125 :
    equal (CleanExpression.polynomial native.placement native.expression125)
        (combination native.relations native.witness125) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression125 native.witness125
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    125 (by decide +kernel) native.idealCodeBinding125 native.idealRelationsBinding native.idealWitnessBinding125

theorem native.preserved125 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression125).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression125 native.placement native.relations native.witness125
    native.checked125 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression126 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨248⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨248⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness126 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨167, by decide⟩)]

theorem native.idealCodeBinding126 :
    CleanIdealChecks.encode native.placement native.expression126 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 126 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding126 :
    NumericPolynomialChecks.encodeCombination native.witness126 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 126 [] := by kernel_rfl

theorem native.idealInputsBinding126 :
    CleanExpression.inputs native.expression126 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 126 [] := by kernel_rfl

theorem native.checked126 :
    equal (CleanExpression.polynomial native.placement native.expression126)
        (combination native.relations native.witness126) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression126 native.witness126
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    126 (by decide +kernel) native.idealCodeBinding126 native.idealRelationsBinding native.idealWitnessBinding126
end Airbender.Compiler.CleanArithmeticNative.BigintCached
