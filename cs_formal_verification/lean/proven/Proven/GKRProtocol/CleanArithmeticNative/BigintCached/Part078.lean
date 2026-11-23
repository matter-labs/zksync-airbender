module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part077
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

local instance generatedBatch78Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch78Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding106 :
    CleanIdealChecks.encode native.placement native.expression106 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 106 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding106 :
    NumericPolynomialChecks.encodeCombination native.witness106 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 106 [] := by kernel_rfl

theorem native.idealInputsBinding106 :
    CleanExpression.inputs native.expression106 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 106 [] := by kernel_rfl

theorem native.checked106 :
    equal (CleanExpression.polynomial native.placement native.expression106)
        (combination native.relations native.witness106) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression106 native.witness106
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    106 (by decide +kernel) native.idealCodeBinding106 native.idealRelationsBinding native.idealWitnessBinding106

theorem native.preserved106 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression106).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression106 native.placement native.relations native.witness106
    native.checked106 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression107 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨91⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨91⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness107 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨148, by decide⟩)]

theorem native.idealCodeBinding107 :
    CleanIdealChecks.encode native.placement native.expression107 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 107 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding107 :
    NumericPolynomialChecks.encodeCombination native.witness107 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 107 [] := by kernel_rfl

theorem native.idealInputsBinding107 :
    CleanExpression.inputs native.expression107 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 107 [] := by kernel_rfl

theorem native.checked107 :
    equal (CleanExpression.polynomial native.placement native.expression107)
        (combination native.relations native.witness107) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression107 native.witness107
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    107 (by decide +kernel) native.idealCodeBinding107 native.idealRelationsBinding native.idealWitnessBinding107

theorem native.preserved107 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression107).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression107 native.placement native.relations native.witness107
    native.checked107 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression108 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨92⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨92⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness108 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨149, by decide⟩)]

theorem native.idealCodeBinding108 :
    CleanIdealChecks.encode native.placement native.expression108 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 108 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding108 :
    NumericPolynomialChecks.encodeCombination native.witness108 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 108 [] := by kernel_rfl

theorem native.idealInputsBinding108 :
    CleanExpression.inputs native.expression108 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 108 [] := by kernel_rfl

theorem native.checked108 :
    equal (CleanExpression.polynomial native.placement native.expression108)
        (combination native.relations native.witness108) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression108 native.witness108
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    108 (by decide +kernel) native.idealCodeBinding108 native.idealRelationsBinding native.idealWitnessBinding108

theorem native.preserved108 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression108).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression108 native.placement native.relations native.witness108
    native.checked108 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression109 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨93⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨93⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness109 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨150, by decide⟩)]

theorem native.idealCodeBinding109 :
    CleanIdealChecks.encode native.placement native.expression109 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 109 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding109 :
    NumericPolynomialChecks.encodeCombination native.witness109 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 109 [] := by kernel_rfl

theorem native.idealInputsBinding109 :
    CleanExpression.inputs native.expression109 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 109 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
