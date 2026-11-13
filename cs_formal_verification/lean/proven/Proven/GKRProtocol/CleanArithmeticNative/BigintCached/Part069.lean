module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part068
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

local instance generatedBatch69Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch69Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding75 :
    NumericPolynomialChecks.encodeCombination native.witness75 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 75 [] := by kernel_rfl

theorem native.idealInputsBinding75 :
    CleanExpression.inputs native.expression75 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 75 [] := by kernel_rfl

theorem native.checked75 :
    equal (CleanExpression.polynomial native.placement native.expression75)
        (combination native.relations native.witness75) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression75 native.witness75
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 75
    (by decide +kernel) native.idealCodeBinding75 native.idealRelationsBinding native.idealWitnessBinding75

theorem native.preserved75 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression75).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression75 native.placement native.relations native.witness75
    native.checked75 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression76 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨76⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨76⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨76⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨22⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨140⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨156⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨76⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨24⟩))

noncomputable def native.witness76 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨122, by decide⟩)]

theorem native.idealCodeBinding76 :
    CleanIdealChecks.encode native.placement native.expression76 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 76 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding76 :
    NumericPolynomialChecks.encodeCombination native.witness76 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 76 [] := by kernel_rfl

theorem native.idealInputsBinding76 :
    CleanExpression.inputs native.expression76 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 76 [] := by kernel_rfl

theorem native.checked76 :
    equal (CleanExpression.polynomial native.placement native.expression76)
        (combination native.relations native.witness76) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression76 native.witness76
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 76
    (by decide +kernel) native.idealCodeBinding76 native.idealRelationsBinding native.idealWitnessBinding76

theorem native.preserved76 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression76).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression76 native.placement native.relations native.witness76
    native.checked76 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression77 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨77⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨77⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨77⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨25⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨141⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨157⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨77⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨27⟩))

noncomputable def native.witness77 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨123, by decide⟩)]

theorem native.idealCodeBinding77 :
    CleanIdealChecks.encode native.placement native.expression77 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 77 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding77 :
    NumericPolynomialChecks.encodeCombination native.witness77 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 77 [] := by kernel_rfl

theorem native.idealInputsBinding77 :
    CleanExpression.inputs native.expression77 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 77 [] := by kernel_rfl

theorem native.checked77 :
    equal (CleanExpression.polynomial native.placement native.expression77)
        (combination native.relations native.witness77) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression77 native.witness77
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 77
    (by decide +kernel) native.idealCodeBinding77 native.idealRelationsBinding native.idealWitnessBinding77

theorem native.preserved77 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression77).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression77 native.placement native.relations native.witness77
    native.checked77 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression78 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨78⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨78⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨78⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨26⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨142⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨158⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨78⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨28⟩))

noncomputable def native.witness78 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨124, by decide⟩)]

theorem native.idealCodeBinding78 :
    CleanIdealChecks.encode native.placement native.expression78 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 78 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding78 :
    NumericPolynomialChecks.encodeCombination native.witness78 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 78 [] := by kernel_rfl

theorem native.idealInputsBinding78 :
    CleanExpression.inputs native.expression78 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 78 [] := by kernel_rfl

theorem native.checked78 :
    equal (CleanExpression.polynomial native.placement native.expression78)
        (combination native.relations native.witness78) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression78 native.witness78
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 78
    (by decide +kernel) native.idealCodeBinding78 native.idealRelationsBinding native.idealWitnessBinding78
end Airbender.Compiler.CleanArithmeticNative.BigintCached
