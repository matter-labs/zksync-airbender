module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
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

local instance generatedBatch82Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch82Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression120 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨230⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨230⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness120 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨161, by decide⟩)]

theorem native.idealCodeBinding120 :
    CleanIdealChecks.encode native.placement native.expression120 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 120 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding120 :
    NumericPolynomialChecks.encodeCombination native.witness120 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 120 [] := by kernel_rfl

theorem native.idealInputsBinding120 :
    CleanExpression.inputs native.expression120 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 120 [] := by kernel_rfl

theorem native.checked120 :
    equal (CleanExpression.polynomial native.placement native.expression120)
        (combination native.relations native.witness120) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression120 native.witness120
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    120 (by decide +kernel) native.idealCodeBinding120 native.idealRelationsBinding native.idealWitnessBinding120

theorem native.preserved120 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression120).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression120 native.placement native.relations native.witness120
    native.checked120 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression121 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨233⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨233⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness121 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨162, by decide⟩)]

theorem native.idealCodeBinding121 :
    CleanIdealChecks.encode native.placement native.expression121 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 121 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding121 :
    NumericPolynomialChecks.encodeCombination native.witness121 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 121 [] := by kernel_rfl

theorem native.idealInputsBinding121 :
    CleanExpression.inputs native.expression121 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 121 [] := by kernel_rfl

theorem native.checked121 :
    equal (CleanExpression.polynomial native.placement native.expression121)
        (combination native.relations native.witness121) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression121 native.witness121
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    121 (by decide +kernel) native.idealCodeBinding121 native.idealRelationsBinding native.idealWitnessBinding121

theorem native.preserved121 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression121).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression121 native.placement native.relations native.witness121
    native.checked121 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression122 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨236⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨236⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness122 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨163, by decide⟩)]

theorem native.idealCodeBinding122 :
    CleanIdealChecks.encode native.placement native.expression122 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 122 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding122 :
    NumericPolynomialChecks.encodeCombination native.witness122 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 122 [] := by kernel_rfl

theorem native.idealInputsBinding122 :
    CleanExpression.inputs native.expression122 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 122 [] := by kernel_rfl

theorem native.checked122 :
    equal (CleanExpression.polynomial native.placement native.expression122)
        (combination native.relations native.witness122) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression122 native.witness122
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    122 (by decide +kernel) native.idealCodeBinding122 native.idealRelationsBinding native.idealWitnessBinding122

theorem native.preserved122 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression122).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression122 native.placement native.relations native.witness122
    native.checked122 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression123 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨239⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨239⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness123 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨164, by decide⟩)]

theorem native.idealCodeBinding123 :
    CleanIdealChecks.encode native.placement native.expression123 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 123 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
