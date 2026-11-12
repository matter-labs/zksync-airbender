module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part069
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

local instance generatedBatch70Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch70Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved78 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression78).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression78 native.placement native.relations native.witness78
    native.checked78 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression79 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨79⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨79⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨79⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨29⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨143⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨159⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨79⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨31⟩))

noncomputable def native.witness79 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨125, by decide⟩)]

theorem native.idealCodeBinding79 :
    CleanIdealChecks.encode native.placement native.expression79 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 79 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding79 :
    NumericPolynomialChecks.encodeCombination native.witness79 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 79 [] := by kernel_rfl

theorem native.idealInputsBinding79 :
    CleanExpression.inputs native.expression79 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 79 [] := by kernel_rfl

theorem native.checked79 :
    equal (CleanExpression.polynomial native.placement native.expression79)
        (combination native.relations native.witness79) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression79 native.witness79
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 79
    (by decide +kernel) native.idealCodeBinding79 native.idealRelationsBinding native.idealWitnessBinding79

theorem native.preserved79 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression79).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression79 native.placement native.relations native.witness79
    native.checked79 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression80 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨80⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨80⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨80⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨30⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨144⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨160⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨80⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨32⟩))

noncomputable def native.witness80 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨126, by decide⟩)]

theorem native.idealCodeBinding80 :
    CleanIdealChecks.encode native.placement native.expression80 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 80 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding80 :
    NumericPolynomialChecks.encodeCombination native.witness80 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 80 [] := by kernel_rfl

theorem native.idealInputsBinding80 :
    CleanExpression.inputs native.expression80 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 80 [] := by kernel_rfl

theorem native.checked80 :
    equal (CleanExpression.polynomial native.placement native.expression80)
        (combination native.relations native.witness80) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression80 native.witness80
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 80
    (by decide +kernel) native.idealCodeBinding80 native.idealRelationsBinding native.idealWitnessBinding80

theorem native.preserved80 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression80).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression80 native.placement native.relations native.witness80
    native.checked80 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression81 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨81⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨81⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨81⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨33⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨145⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨161⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨81⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨35⟩))

noncomputable def native.witness81 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨127, by decide⟩)]

theorem native.idealCodeBinding81 :
    CleanIdealChecks.encode native.placement native.expression81 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 81 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding81 :
    NumericPolynomialChecks.encodeCombination native.witness81 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 81 [] := by kernel_rfl

theorem native.idealInputsBinding81 :
    CleanExpression.inputs native.expression81 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 81 [] := by kernel_rfl

theorem native.checked81 :
    equal (CleanExpression.polynomial native.placement native.expression81)
        (combination native.relations native.witness81) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression81 native.witness81
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 81
    (by decide +kernel) native.idealCodeBinding81 native.idealRelationsBinding native.idealWitnessBinding81

theorem native.preserved81 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression81).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression81 native.placement native.relations native.witness81
    native.checked81 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression82 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨82⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨82⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨82⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨34⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨146⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨162⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨82⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨36⟩))

noncomputable def native.witness82 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨128, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BigintCached
