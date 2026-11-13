module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part063
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

local instance generatedBatch64Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch64Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding58 :
    CleanIdealChecks.encode native.placement native.expression58 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 58 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding58 :
    NumericPolynomialChecks.encodeCombination native.witness58 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 58 [] := by kernel_rfl

theorem native.idealInputsBinding58 :
    CleanExpression.inputs native.expression58 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 58 [] := by kernel_rfl

theorem native.checked58 :
    equal (CleanExpression.polynomial native.placement native.expression58)
        (combination native.relations native.witness58) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression58 native.witness58
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 58
    (by decide +kernel) native.idealCodeBinding58 native.idealRelationsBinding native.idealWitnessBinding58

theorem native.preserved58 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression58).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression58 native.placement native.relations native.witness58
    native.checked58 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression59 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨202⟩)
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
                        (Airbender.Expression.var ⟨75⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨75⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨75⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨75⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨75⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨139⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨139⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness59 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨50, by decide⟩)]

theorem native.idealCodeBinding59 :
    CleanIdealChecks.encode native.placement native.expression59 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 59 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding59 :
    NumericPolynomialChecks.encodeCombination native.witness59 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 59 [] := by kernel_rfl

theorem native.idealInputsBinding59 :
    CleanExpression.inputs native.expression59 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 59 [] := by kernel_rfl

theorem native.checked59 :
    equal (CleanExpression.polynomial native.placement native.expression59)
        (combination native.relations native.witness59) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression59 native.witness59
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 59
    (by decide +kernel) native.idealCodeBinding59 native.idealRelationsBinding native.idealWitnessBinding59

theorem native.preserved59 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression59).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression59 native.placement native.relations native.witness59
    native.checked59 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression60 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨203⟩)
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
                        (Airbender.Expression.var ⟨76⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨76⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨76⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨76⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨76⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨140⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨140⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness60 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨51, by decide⟩)]

theorem native.idealCodeBinding60 :
    CleanIdealChecks.encode native.placement native.expression60 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 60 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding60 :
    NumericPolynomialChecks.encodeCombination native.witness60 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 60 [] := by kernel_rfl

theorem native.idealInputsBinding60 :
    CleanExpression.inputs native.expression60 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 60 [] := by kernel_rfl

theorem native.checked60 :
    equal (CleanExpression.polynomial native.placement native.expression60)
        (combination native.relations native.witness60) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression60 native.witness60
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 60
    (by decide +kernel) native.idealCodeBinding60 native.idealRelationsBinding native.idealWitnessBinding60

theorem native.preserved60 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression60).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression60 native.placement native.relations native.witness60
    native.checked60 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression61 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨204⟩)
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
                        (Airbender.Expression.var ⟨77⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨77⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨77⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨77⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨77⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨141⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨141⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness61 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨52, by decide⟩)]

theorem native.idealCodeBinding61 :
    CleanIdealChecks.encode native.placement native.expression61 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 61 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding61 :
    NumericPolynomialChecks.encodeCombination native.witness61 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 61 [] := by kernel_rfl

theorem native.idealInputsBinding61 :
    CleanExpression.inputs native.expression61 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 61 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
