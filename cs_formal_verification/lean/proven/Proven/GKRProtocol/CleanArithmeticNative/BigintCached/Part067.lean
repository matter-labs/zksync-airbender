module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part066
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

local instance generatedBatch67Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch67Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding68 :
    CleanExpression.inputs native.expression68 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 68 [] := by kernel_rfl

theorem native.checked68 :
    equal (CleanExpression.polynomial native.placement native.expression68)
        (combination native.relations native.witness68) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression68 native.witness68
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 68
    (by decide +kernel) native.idealCodeBinding68 native.idealRelationsBinding native.idealWitnessBinding68

theorem native.preserved68 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression68).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression68 native.placement native.relations native.witness68
    native.checked68 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression69 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨69⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨69⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨69⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨9⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨133⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨149⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨69⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨11⟩))

noncomputable def native.witness69 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨115, by decide⟩)]

theorem native.idealCodeBinding69 :
    CleanIdealChecks.encode native.placement native.expression69 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 69 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding69 :
    NumericPolynomialChecks.encodeCombination native.witness69 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 69 [] := by kernel_rfl

theorem native.idealInputsBinding69 :
    CleanExpression.inputs native.expression69 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 69 [] := by kernel_rfl

theorem native.checked69 :
    equal (CleanExpression.polynomial native.placement native.expression69)
        (combination native.relations native.witness69) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression69 native.witness69
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 69
    (by decide +kernel) native.idealCodeBinding69 native.idealRelationsBinding native.idealWitnessBinding69

theorem native.preserved69 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression69).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression69 native.placement native.relations native.witness69
    native.checked69 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression70 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨70⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨70⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨70⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨10⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨134⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨150⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨70⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨12⟩))

noncomputable def native.witness70 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨116, by decide⟩)]

theorem native.idealCodeBinding70 :
    CleanIdealChecks.encode native.placement native.expression70 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 70 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding70 :
    NumericPolynomialChecks.encodeCombination native.witness70 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 70 [] := by kernel_rfl

theorem native.idealInputsBinding70 :
    CleanExpression.inputs native.expression70 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 70 [] := by kernel_rfl

theorem native.checked70 :
    equal (CleanExpression.polynomial native.placement native.expression70)
        (combination native.relations native.witness70) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression70 native.witness70
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 70
    (by decide +kernel) native.idealCodeBinding70 native.idealRelationsBinding native.idealWitnessBinding70

theorem native.preserved70 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression70).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression70 native.placement native.relations native.witness70
    native.checked70 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression71 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨71⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨71⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨71⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨13⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨135⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨151⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨71⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨15⟩))

noncomputable def native.witness71 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨117, by decide⟩)]

theorem native.idealCodeBinding71 :
    CleanIdealChecks.encode native.placement native.expression71 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 71 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding71 :
    NumericPolynomialChecks.encodeCombination native.witness71 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 71 [] := by kernel_rfl

theorem native.idealInputsBinding71 :
    CleanExpression.inputs native.expression71 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 71 [] := by kernel_rfl

theorem native.checked71 :
    equal (CleanExpression.polynomial native.placement native.expression71)
        (combination native.relations native.witness71) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression71 native.witness71
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 71
    (by decide +kernel) native.idealCodeBinding71 native.idealRelationsBinding native.idealWitnessBinding71

theorem native.preserved71 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression71).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression71 native.placement native.relations native.witness71
    native.checked71 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
