module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part065
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

local instance generatedBatch66Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch66Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness65 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨56, by decide⟩)]

theorem native.idealCodeBinding65 :
    CleanIdealChecks.encode native.placement native.expression65 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 65 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding65 :
    NumericPolynomialChecks.encodeCombination native.witness65 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 65 [] := by kernel_rfl

theorem native.idealInputsBinding65 :
    CleanExpression.inputs native.expression65 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 65 [] := by kernel_rfl

theorem native.checked65 :
    equal (CleanExpression.polynomial native.placement native.expression65)
        (combination native.relations native.witness65) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression65 native.witness65
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 65
    (by decide +kernel) native.idealCodeBinding65 native.idealRelationsBinding native.idealWitnessBinding65

theorem native.preserved65 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression65).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression65 native.placement native.relations native.witness65
    native.checked65 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression66 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨209⟩)
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
                        (Airbender.Expression.var ⟨82⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨82⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨82⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨82⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨82⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨146⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨146⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness66 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨57, by decide⟩)]

theorem native.idealCodeBinding66 :
    CleanIdealChecks.encode native.placement native.expression66 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 66 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding66 :
    NumericPolynomialChecks.encodeCombination native.witness66 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 66 [] := by kernel_rfl

theorem native.idealInputsBinding66 :
    CleanExpression.inputs native.expression66 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 66 [] := by kernel_rfl

theorem native.checked66 :
    equal (CleanExpression.polynomial native.placement native.expression66)
        (combination native.relations native.witness66) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression66 native.witness66
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 66
    (by decide +kernel) native.idealCodeBinding66 native.idealRelationsBinding native.idealWitnessBinding66

theorem native.preserved66 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression66).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression66 native.placement native.relations native.witness66
    native.checked66 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression67 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨67⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨67⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨67⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨5⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨131⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨147⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨67⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨7⟩))

noncomputable def native.witness67 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨113, by decide⟩)]

theorem native.idealCodeBinding67 :
    CleanIdealChecks.encode native.placement native.expression67 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 67 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding67 :
    NumericPolynomialChecks.encodeCombination native.witness67 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 67 [] := by kernel_rfl

theorem native.idealInputsBinding67 :
    CleanExpression.inputs native.expression67 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 67 [] := by kernel_rfl

theorem native.checked67 :
    equal (CleanExpression.polynomial native.placement native.expression67)
        (combination native.relations native.witness67) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression67 native.witness67
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 67
    (by decide +kernel) native.idealCodeBinding67 native.idealRelationsBinding native.idealWitnessBinding67

theorem native.preserved67 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression67).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression67 native.placement native.relations native.witness67
    native.checked67 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression68 : Airbender.Expression Source.BaseField :=
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
                      (Airbender.Expression.var ⟨68⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨68⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨68⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨6⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨132⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨148⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨68⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨8⟩))

noncomputable def native.witness68 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨114, by decide⟩)]

theorem native.idealCodeBinding68 :
    CleanIdealChecks.encode native.placement native.expression68 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 68 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding68 :
    NumericPolynomialChecks.encodeCombination native.witness68 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 68 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
