module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part052
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

local instance generatedBatch53Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch53Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding136 :
    NumericPolynomialChecks.encodeCombination native.witness136 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 136 [] := by kernel_rfl

theorem native.idealInputsBinding136 :
    CleanExpression.inputs native.expression136 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 136 [] := by kernel_rfl

theorem native.checked136 :
    equal (CleanExpression.polynomial native.placement native.expression136)
        (combination native.relations native.witness136) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression136 native.witness136
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    136 (by decide +kernel) native.idealCodeBinding136 native.idealRelationsBinding native.idealWitnessBinding136

theorem native.preserved136 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression136).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression136 native.placement native.relations native.witness136
    native.checked136 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression137 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨32⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨34⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness137 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨169, by decide⟩)]

theorem native.idealCodeBinding137 :
    CleanIdealChecks.encode native.placement native.expression137 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 137 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding137 :
    NumericPolynomialChecks.encodeCombination native.witness137 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 137 [] := by kernel_rfl

theorem native.idealInputsBinding137 :
    CleanExpression.inputs native.expression137 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 137 [] := by kernel_rfl

theorem native.checked137 :
    equal (CleanExpression.polynomial native.placement native.expression137)
        (combination native.relations native.witness137) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression137 native.witness137
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    137 (by decide +kernel) native.idealCodeBinding137 native.idealRelationsBinding native.idealWitnessBinding137

theorem native.preserved137 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression137).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression137 native.placement native.relations native.witness137
    native.checked137 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression138 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨35⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨37⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness138 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨170, by decide⟩)]

theorem native.idealCodeBinding138 :
    CleanIdealChecks.encode native.placement native.expression138 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 138 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding138 :
    NumericPolynomialChecks.encodeCombination native.witness138 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 138 [] := by kernel_rfl

theorem native.idealInputsBinding138 :
    CleanExpression.inputs native.expression138 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 138 [] := by kernel_rfl

theorem native.checked138 :
    equal (CleanExpression.polynomial native.placement native.expression138)
        (combination native.relations native.witness138) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression138 native.witness138
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    138 (by decide +kernel) native.idealCodeBinding138 native.idealRelationsBinding native.idealWitnessBinding138

theorem native.preserved138 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression138).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression138 native.placement native.relations native.witness138
    native.checked138 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression139 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨36⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨38⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness139 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨171, by decide⟩)]

theorem native.idealCodeBinding139 :
    CleanIdealChecks.encode native.placement native.expression139 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 139 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding139 :
    NumericPolynomialChecks.encodeCombination native.witness139 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 139 [] := by kernel_rfl

theorem native.idealInputsBinding139 :
    CleanExpression.inputs native.expression139 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 139 [] := by kernel_rfl

theorem native.checked139 :
    equal (CleanExpression.polynomial native.placement native.expression139)
        (combination native.relations native.witness139) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression139 native.witness139
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    139 (by decide +kernel) native.idealCodeBinding139 native.idealRelationsBinding native.idealWitnessBinding139
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
