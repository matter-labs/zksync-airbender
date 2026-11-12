module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part061
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

local instance generatedBatch62Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch62Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding51 :
    NumericPolynomialChecks.encodeCombination native.witness51 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 51 [] := by kernel_rfl

theorem native.idealInputsBinding51 :
    CleanExpression.inputs native.expression51 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 51 [] := by kernel_rfl

theorem native.checked51 :
    equal (CleanExpression.polynomial native.placement native.expression51)
        (combination native.relations native.witness51) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression51 native.witness51
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 51
    (by decide +kernel) native.idealCodeBinding51 native.idealRelationsBinding native.idealWitnessBinding51

theorem native.preserved51 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression51).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression51 native.placement native.relations native.witness51
    native.checked51 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression52 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨195⟩)
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
                        (Airbender.Expression.var ⟨68⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨68⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨68⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨68⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨68⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨132⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨132⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness52 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨43, by decide⟩)]

theorem native.idealCodeBinding52 :
    CleanIdealChecks.encode native.placement native.expression52 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 52 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding52 :
    NumericPolynomialChecks.encodeCombination native.witness52 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 52 [] := by kernel_rfl

theorem native.idealInputsBinding52 :
    CleanExpression.inputs native.expression52 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 52 [] := by kernel_rfl

theorem native.checked52 :
    equal (CleanExpression.polynomial native.placement native.expression52)
        (combination native.relations native.witness52) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression52 native.witness52
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 52
    (by decide +kernel) native.idealCodeBinding52 native.idealRelationsBinding native.idealWitnessBinding52

theorem native.preserved52 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression52).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression52 native.placement native.relations native.witness52
    native.checked52 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression53 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨196⟩)
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
                        (Airbender.Expression.var ⟨69⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨69⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨69⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨69⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨69⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨133⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨133⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness53 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨44, by decide⟩)]

theorem native.idealCodeBinding53 :
    CleanIdealChecks.encode native.placement native.expression53 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 53 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding53 :
    NumericPolynomialChecks.encodeCombination native.witness53 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 53 [] := by kernel_rfl

theorem native.idealInputsBinding53 :
    CleanExpression.inputs native.expression53 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 53 [] := by kernel_rfl

theorem native.checked53 :
    equal (CleanExpression.polynomial native.placement native.expression53)
        (combination native.relations native.witness53) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression53 native.witness53
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 53
    (by decide +kernel) native.idealCodeBinding53 native.idealRelationsBinding native.idealWitnessBinding53

theorem native.preserved53 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression53).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression53 native.placement native.relations native.witness53
    native.checked53 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression54 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨197⟩)
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
                        (Airbender.Expression.var ⟨70⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨70⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨70⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨70⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨70⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨134⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨134⟩))
          (Airbender.Expression.var ⟨63⟩))))

noncomputable def native.witness54 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨45, by decide⟩)]

theorem native.idealCodeBinding54 :
    CleanIdealChecks.encode native.placement native.expression54 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 54 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding54 :
    NumericPolynomialChecks.encodeCombination native.witness54 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 54 [] := by kernel_rfl

theorem native.idealInputsBinding54 :
    CleanExpression.inputs native.expression54 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 54 [] := by kernel_rfl

theorem native.checked54 :
    equal (CleanExpression.polynomial native.placement native.expression54)
        (combination native.relations native.witness54) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression54 native.witness54
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 54
    (by decide +kernel) native.idealCodeBinding54 native.idealRelationsBinding native.idealWitnessBinding54
end Airbender.Compiler.CleanArithmeticNative.BigintCached
