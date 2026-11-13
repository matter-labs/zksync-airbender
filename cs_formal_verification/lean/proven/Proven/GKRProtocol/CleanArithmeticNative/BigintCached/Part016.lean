module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part015
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

local instance generatedBatch16Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch16Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding9 :
    CleanExpression.inputs native.expression9 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 9 [] := by kernel_rfl

theorem native.checked9 :
    equal (CleanExpression.polynomial native.placement native.expression9)
        (combination native.relations native.witness9) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression9 native.witness9
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 9
    (by decide +kernel) native.idealCodeBinding9 native.idealRelationsBinding native.idealWitnessBinding9

theorem native.preserved9 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression9).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression9 native.placement native.relations native.witness9
    native.checked9 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression10 : Airbender.Expression Source.BaseField :=
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
                              (Airbender.Expression.var ⟨18⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨74⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨18⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨74⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨46⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨46⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨74⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨46⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨46⟩))
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
                        (Airbender.Expression.var ⟨74⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨18⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨46⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨18⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨74⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨89⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨90⟩))

noncomputable def native.witness10 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨72, by decide⟩)]

theorem native.idealCodeBinding10 :
    CleanIdealChecks.encode native.placement native.expression10 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 10 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding10 :
    NumericPolynomialChecks.encodeCombination native.witness10 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 10 [] := by kernel_rfl

theorem native.idealInputsBinding10 :
    CleanExpression.inputs native.expression10 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 10 [] := by kernel_rfl

theorem native.checked10 :
    equal (CleanExpression.polynomial native.placement native.expression10)
        (combination native.relations native.witness10) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression10 native.witness10
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 10
    (by decide +kernel) native.idealCodeBinding10 native.idealRelationsBinding native.idealWitnessBinding10

theorem native.preserved10 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression10).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression10 native.placement native.relations native.witness10
    native.checked10 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression11 : Airbender.Expression Source.BaseField :=
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
                              (Airbender.Expression.var ⟨21⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨75⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨21⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨75⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨47⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨47⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨75⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨47⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨47⟩))
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
                        (Airbender.Expression.var ⟨75⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨21⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨47⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨21⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨75⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨90⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨91⟩))

noncomputable def native.witness11 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨73, by decide⟩)]

theorem native.idealCodeBinding11 :
    CleanIdealChecks.encode native.placement native.expression11 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 11 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding11 :
    NumericPolynomialChecks.encodeCombination native.witness11 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 11 [] := by kernel_rfl

theorem native.idealInputsBinding11 :
    CleanExpression.inputs native.expression11 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 11 [] := by kernel_rfl

theorem native.checked11 :
    equal (CleanExpression.polynomial native.placement native.expression11)
        (combination native.relations native.witness11) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression11 native.witness11
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 11
    (by decide +kernel) native.idealCodeBinding11 native.idealRelationsBinding native.idealWitnessBinding11

theorem native.preserved11 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression11).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression11 native.placement native.relations native.witness11
    native.checked11 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression12 : Airbender.Expression Source.BaseField :=
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
                              (Airbender.Expression.var ⟨22⟩))
                            (Airbender.Expression.var ⟨59⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨76⟩))
                          (Airbender.Expression.var ⟨60⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨22⟩))
                        (Airbender.Expression.var ⟨61⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨76⟩))
                      (Airbender.Expression.var ⟨64⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨48⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨48⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨76⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨48⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨48⟩))
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
                        (Airbender.Expression.var ⟨76⟩))
                      (Airbender.Expression.var ⟨59⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨22⟩))
                    (Airbender.Expression.var ⟨60⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨48⟩))
                  (Airbender.Expression.var ⟨61⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨22⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨76⟩))
              (Airbender.Expression.var ⟨66⟩)))))
      (Airbender.Expression.var ⟨91⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
      (Airbender.Expression.var ⟨92⟩))

noncomputable def native.witness12 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨74, by decide⟩)]

theorem native.idealCodeBinding12 :
    CleanIdealChecks.encode native.placement native.expression12 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 12 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding12 :
    NumericPolynomialChecks.encodeCombination native.witness12 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 12 [] := by kernel_rfl

theorem native.idealInputsBinding12 :
    CleanExpression.inputs native.expression12 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 12 [] := by kernel_rfl

theorem native.checked12 :
    equal (CleanExpression.polynomial native.placement native.expression12)
        (combination native.relations native.witness12) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression12 native.witness12
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 12
    (by decide +kernel) native.idealCodeBinding12 native.idealRelationsBinding native.idealWitnessBinding12

theorem native.preserved12 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression12).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression12 native.placement native.relations native.witness12
    native.checked12 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
