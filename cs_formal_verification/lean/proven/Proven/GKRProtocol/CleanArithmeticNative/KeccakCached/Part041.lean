module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part040
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.KeccakCached
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCached
public import Proven.GKRProtocol.CleanPlacementNative.KeccakCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch41Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch41Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding95 :
    CleanIdealChecks.encode native.placement native.expression95 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 95 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding95 :
    NumericPolynomialChecks.encodeCombination native.witness95 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 95 [] := by kernel_rfl

theorem native.idealInputsBinding95 :
    CleanExpression.inputs native.expression95 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 95 [] := by kernel_rfl

theorem native.checked95 :
    equal (CleanExpression.polynomial native.placement native.expression95)
        (combination native.relations native.witness95) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression95 native.witness95
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 95
    (by decide +kernel) native.idealCodeBinding95 native.idealRelationsBinding native.idealWitnessBinding95

theorem native.preserved95 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression95).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression95 native.placement native.relations native.witness95
    native.checked95 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression96 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨47⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨49⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness96 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨128, by decide⟩)]

theorem native.idealCodeBinding96 :
    CleanIdealChecks.encode native.placement native.expression96 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 96 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding96 :
    NumericPolynomialChecks.encodeCombination native.witness96 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 96 [] := by kernel_rfl

theorem native.idealInputsBinding96 :
    CleanExpression.inputs native.expression96 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 96 [] := by kernel_rfl

theorem native.checked96 :
    equal (CleanExpression.polynomial native.placement native.expression96)
        (combination native.relations native.witness96) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression96 native.witness96
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 96
    (by decide +kernel) native.idealCodeBinding96 native.idealRelationsBinding native.idealWitnessBinding96

theorem native.preserved96 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression96).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression96 native.placement native.relations native.witness96
    native.checked96 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression97 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨48⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨50⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness97 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨129, by decide⟩)]

theorem native.idealCodeBinding97 :
    CleanIdealChecks.encode native.placement native.expression97 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 97 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding97 :
    NumericPolynomialChecks.encodeCombination native.witness97 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 97 [] := by kernel_rfl

theorem native.idealInputsBinding97 :
    CleanExpression.inputs native.expression97 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 97 [] := by kernel_rfl

theorem native.checked97 :
    equal (CleanExpression.polynomial native.placement native.expression97)
        (combination native.relations native.witness97) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression97 native.witness97
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 97
    (by decide +kernel) native.idealCodeBinding97 native.idealRelationsBinding native.idealWitnessBinding97

theorem native.preserved97 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression97).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression97 native.placement native.relations native.witness97
    native.checked97 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression98 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨51⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨53⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness98 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨130, by decide⟩)]

theorem native.idealCodeBinding98 :
    CleanIdealChecks.encode native.placement native.expression98 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 98 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding98 :
    NumericPolynomialChecks.encodeCombination native.witness98 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 98 [] := by kernel_rfl

theorem native.idealInputsBinding98 :
    CleanExpression.inputs native.expression98 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 98 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
