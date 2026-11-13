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

local instance generatedBatch75Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch75Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression96 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨64⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨64⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness96 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨137, by decide⟩)]

theorem native.idealCodeBinding96 :
    CleanIdealChecks.encode native.placement native.expression96 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 96 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding96 :
    NumericPolynomialChecks.encodeCombination native.witness96 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 96 [] := by kernel_rfl

theorem native.idealInputsBinding96 :
    CleanExpression.inputs native.expression96 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 96 [] := by kernel_rfl

theorem native.checked96 :
    equal (CleanExpression.polynomial native.placement native.expression96)
        (combination native.relations native.witness96) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression96 native.witness96
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 96
    (by decide +kernel) native.idealCodeBinding96 native.idealRelationsBinding native.idealWitnessBinding96

theorem native.preserved96 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression96).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression96 native.placement native.relations native.witness96
    native.checked96 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression97 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨65⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨65⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness97 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨138, by decide⟩)]

theorem native.idealCodeBinding97 :
    CleanIdealChecks.encode native.placement native.expression97 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 97 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding97 :
    NumericPolynomialChecks.encodeCombination native.witness97 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 97 [] := by kernel_rfl

theorem native.idealInputsBinding97 :
    CleanExpression.inputs native.expression97 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 97 [] := by kernel_rfl

theorem native.checked97 :
    equal (CleanExpression.polynomial native.placement native.expression97)
        (combination native.relations native.witness97) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression97 native.witness97
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 97
    (by decide +kernel) native.idealCodeBinding97 native.idealRelationsBinding native.idealWitnessBinding97

theorem native.preserved97 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression97).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression97 native.placement native.relations native.witness97
    native.checked97 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression98 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨66⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨66⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness98 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨139, by decide⟩)]

theorem native.idealCodeBinding98 :
    CleanIdealChecks.encode native.placement native.expression98 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 98 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding98 :
    NumericPolynomialChecks.encodeCombination native.witness98 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 98 [] := by kernel_rfl

theorem native.idealInputsBinding98 :
    CleanExpression.inputs native.expression98 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 98 [] := by kernel_rfl

theorem native.checked98 :
    equal (CleanExpression.polynomial native.placement native.expression98)
        (combination native.relations native.witness98) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression98 native.witness98
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 98
    (by decide +kernel) native.idealCodeBinding98 native.idealRelationsBinding native.idealWitnessBinding98

theorem native.preserved98 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression98).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression98 native.placement native.relations native.witness98
    native.checked98 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression99 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨83⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨83⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness99 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨140, by decide⟩)]

theorem native.idealCodeBinding99 :
    CleanIdealChecks.encode native.placement native.expression99 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 99 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
