module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
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

local instance generatedBatch17Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch17Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression13 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
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
                              (Airbender.Expression.var ⟨25⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨77⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨25⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨77⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨49⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨49⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨77⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨49⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨49⟩))
            (Airbender.Expression.var ⟨66⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
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
                      (Airbender.Expression.var ⟨25⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨49⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨25⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨77⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨92⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨93⟩))

noncomputable def native.witness13 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨75, by decide⟩)]

theorem native.idealCodeBinding13 :
    CleanIdealChecks.encode native.placement native.expression13 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 13 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding13 :
    NumericPolynomialChecks.encodeCombination native.witness13 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 13 [] := by kernel_rfl

theorem native.idealInputsBinding13 :
    CleanExpression.inputs native.expression13 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 13 [] := by kernel_rfl

theorem native.checked13 :
    equal (CleanExpression.polynomial native.placement native.expression13)
        (combination native.relations native.witness13) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression13 native.witness13
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 13
    (by decide +kernel) native.idealCodeBinding13 native.idealRelationsBinding native.idealWitnessBinding13

theorem native.preserved13 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression13).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression13 native.placement native.relations native.witness13
    native.checked13 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression14 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
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
                              (Airbender.Expression.var ⟨26⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨78⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨26⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨78⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨50⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨50⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨78⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨50⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨50⟩))
            (Airbender.Expression.var ⟨66⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨78⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨26⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨50⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨26⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨78⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨93⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨94⟩))

noncomputable def native.witness14 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨76, by decide⟩)]

theorem native.idealCodeBinding14 :
    CleanIdealChecks.encode native.placement native.expression14 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 14 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding14 :
    NumericPolynomialChecks.encodeCombination native.witness14 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 14 [] := by kernel_rfl

theorem native.idealInputsBinding14 :
    CleanExpression.inputs native.expression14 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 14 [] := by kernel_rfl

theorem native.checked14 :
    equal (CleanExpression.polynomial native.placement native.expression14)
        (combination native.relations native.witness14) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression14 native.witness14
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 14
    (by decide +kernel) native.idealCodeBinding14 native.idealRelationsBinding native.idealWitnessBinding14

theorem native.preserved14 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression14).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression14 native.placement native.relations native.witness14
    native.checked14 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression15 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
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
                              (Airbender.Expression.var ⟨29⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨79⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨29⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨79⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨51⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨51⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨79⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨51⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨51⟩))
            (Airbender.Expression.var ⟨66⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨79⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨29⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨51⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨29⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨79⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨94⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨95⟩))

noncomputable def native.witness15 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨77, by decide⟩)]

theorem native.idealCodeBinding15 :
    CleanIdealChecks.encode native.placement native.expression15 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 15 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding15 :
    NumericPolynomialChecks.encodeCombination native.witness15 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 15 [] := by kernel_rfl

theorem native.idealInputsBinding15 :
    CleanExpression.inputs native.expression15 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 15 [] := by kernel_rfl

theorem native.checked15 :
    equal (CleanExpression.polynomial native.placement native.expression15)
        (combination native.relations native.witness15) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression15 native.witness15
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 15
    (by decide +kernel) native.idealCodeBinding15 native.idealRelationsBinding native.idealWitnessBinding15

theorem native.preserved15 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression15).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression15 native.placement native.relations native.witness15
    native.checked15 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression16 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
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
                              (Airbender.Expression.var ⟨30⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨80⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨30⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨80⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨52⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨52⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨80⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨52⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨52⟩))
            (Airbender.Expression.var ⟨66⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨80⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨30⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨52⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨30⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨80⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨95⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨96⟩))

noncomputable def native.witness16 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨78, by decide⟩)]

theorem native.idealCodeBinding16 :
    CleanIdealChecks.encode native.placement native.expression16 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 16 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
