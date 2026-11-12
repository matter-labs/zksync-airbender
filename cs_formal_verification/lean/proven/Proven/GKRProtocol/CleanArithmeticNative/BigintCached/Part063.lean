module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part062
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

local instance generatedBatch63Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch63Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved54 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression54).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression54 native.placement native.relations native.witness54
    native.checked54 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression55 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨198⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
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
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨71⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨71⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨71⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨135⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨135⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness55 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨46, by decide⟩)]

theorem native.idealCodeBinding55 :
    CleanIdealChecks.encode native.placement native.expression55 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 55 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding55 :
    NumericPolynomialChecks.encodeCombination native.witness55 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 55 [] := by kernel_rfl

theorem native.idealInputsBinding55 :
    CleanExpression.inputs native.expression55 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 55 [] := by kernel_rfl

theorem native.checked55 :
    equal (CleanExpression.polynomial native.placement native.expression55)
        (combination native.relations native.witness55) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression55 native.witness55
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 55
    (by decide +kernel) native.idealCodeBinding55 native.idealRelationsBinding native.idealWitnessBinding55

theorem native.preserved55 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression55).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression55 native.placement native.relations native.witness55
    native.checked55 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression56 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨199⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨72⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨72⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨72⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨72⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨72⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨136⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨136⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness56 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨47, by decide⟩)]

theorem native.idealCodeBinding56 :
    CleanIdealChecks.encode native.placement native.expression56 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 56 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding56 :
    NumericPolynomialChecks.encodeCombination native.witness56 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 56 [] := by kernel_rfl

theorem native.idealInputsBinding56 :
    CleanExpression.inputs native.expression56 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 56 [] := by kernel_rfl

theorem native.checked56 :
    equal (CleanExpression.polynomial native.placement native.expression56)
        (combination native.relations native.witness56) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression56 native.witness56
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 56
    (by decide +kernel) native.idealCodeBinding56 native.idealRelationsBinding native.idealWitnessBinding56

theorem native.preserved56 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression56).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression56 native.placement native.relations native.witness56
    native.checked56 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression57 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨200⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨73⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨73⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨73⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨73⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨73⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨137⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨137⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness57 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨48, by decide⟩)]

theorem native.idealCodeBinding57 :
    CleanIdealChecks.encode native.placement native.expression57 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 57 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding57 :
    NumericPolynomialChecks.encodeCombination native.witness57 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 57 [] := by kernel_rfl

theorem native.idealInputsBinding57 :
    CleanExpression.inputs native.expression57 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 57 [] := by kernel_rfl

theorem native.checked57 :
    equal (CleanExpression.polynomial native.placement native.expression57)
        (combination native.relations native.witness57) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression57 native.witness57
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 57
    (by decide +kernel) native.idealCodeBinding57 native.idealRelationsBinding native.idealWitnessBinding57

theorem native.preserved57 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression57).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression57 native.placement native.relations native.witness57
    native.checked57 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression58 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨201⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨74⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨74⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨74⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨74⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨74⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨138⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨138⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness58 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨49, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BigintCached
