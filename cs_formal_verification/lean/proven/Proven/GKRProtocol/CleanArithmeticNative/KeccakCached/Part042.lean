module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part041
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

local instance generatedBatch42Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch42Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked98 :
    equal (CleanExpression.polynomial native.placement native.expression98)
        (combination native.relations native.witness98) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression98 native.witness98
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 98
    (by decide +kernel) native.idealCodeBinding98 native.idealRelationsBinding native.idealWitnessBinding98

theorem native.preserved98 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression98).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression98 native.placement native.relations native.witness98
    native.checked98 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression99 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨52⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨54⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness99 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨131, by decide⟩)]

theorem native.idealCodeBinding99 :
    CleanIdealChecks.encode native.placement native.expression99 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 99 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding99 :
    NumericPolynomialChecks.encodeCombination native.witness99 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 99 [] := by kernel_rfl

theorem native.idealInputsBinding99 :
    CleanExpression.inputs native.expression99 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 99 [] := by kernel_rfl

theorem native.checked99 :
    equal (CleanExpression.polynomial native.placement native.expression99)
        (combination native.relations native.witness99) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression99 native.witness99
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 99
    (by decide +kernel) native.idealCodeBinding99 native.idealRelationsBinding native.idealWitnessBinding99

theorem native.preserved99 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression99).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression99 native.placement native.relations native.witness99
    native.checked99 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression100 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨23⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨25⟩))))
    (Airbender.Expression.var ⟨64⟩)

noncomputable def native.witness100 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨132, by decide⟩)]

theorem native.idealCodeBinding100 :
    CleanIdealChecks.encode native.placement native.expression100 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 100 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding100 :
    NumericPolynomialChecks.encodeCombination native.witness100 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 100 [] := by kernel_rfl

theorem native.idealInputsBinding100 :
    CleanExpression.inputs native.expression100 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 100 [] := by kernel_rfl

theorem native.checked100 :
    equal (CleanExpression.polynomial native.placement native.expression100)
        (combination native.relations native.witness100) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression100 native.witness100
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    100 (by decide +kernel) native.idealCodeBinding100 native.idealRelationsBinding native.idealWitnessBinding100

theorem native.preserved100 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression100).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression100 native.placement native.relations native.witness100
    native.checked100 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression101 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨24⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨26⟩))))
    (Airbender.Expression.var ⟨64⟩)

noncomputable def native.witness101 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨133, by decide⟩)]

theorem native.idealCodeBinding101 :
    CleanIdealChecks.encode native.placement native.expression101 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 101 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding101 :
    NumericPolynomialChecks.encodeCombination native.witness101 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 101 [] := by kernel_rfl

theorem native.idealInputsBinding101 :
    CleanExpression.inputs native.expression101 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 101 [] := by kernel_rfl

theorem native.checked101 :
    equal (CleanExpression.polynomial native.placement native.expression101)
        (combination native.relations native.witness101) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression101 native.witness101
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    101 (by decide +kernel) native.idealCodeBinding101 native.idealRelationsBinding native.idealWitnessBinding101

theorem native.preserved101 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression101).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression101 native.placement native.relations native.witness101
    native.checked101 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression102 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨27⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨29⟩))))
    (Airbender.Expression.var ⟨64⟩)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
