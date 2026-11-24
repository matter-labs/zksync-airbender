module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part014
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

local instance generatedBatch15Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch15Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness6 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨38, by decide⟩)]

theorem native.idealCodeBinding6 :
    CleanIdealChecks.encode native.placement native.expression6 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 6 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding6 :
    NumericPolynomialChecks.encodeCombination native.witness6 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 6 [] := by kernel_rfl

theorem native.idealInputsBinding6 :
    CleanExpression.inputs native.expression6 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 6 [] := by kernel_rfl

theorem native.checked6 :
    equal (CleanExpression.polynomial native.placement native.expression6)
        (combination native.relations native.witness6) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression6 native.witness6
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 6
    (by decide +kernel) native.idealCodeBinding6 native.idealRelationsBinding native.idealWitnessBinding6

theorem native.preserved6 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression6).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression6 native.placement native.relations native.witness6
    native.checked6 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression7 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨0⟩))))
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨70⟩))
            (Airbender.Expression.var ⟨71⟩))
          (Airbender.Expression.var ⟨72⟩))
        (Airbender.Expression.var ⟨73⟩))
      (Airbender.Expression.var ⟨74⟩))

noncomputable def native.witness7 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨39, by decide⟩)]

theorem native.idealCodeBinding7 :
    CleanIdealChecks.encode native.placement native.expression7 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 7 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding7 :
    NumericPolynomialChecks.encodeCombination native.witness7 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 7 [] := by kernel_rfl

theorem native.idealInputsBinding7 :
    CleanExpression.inputs native.expression7 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 7 [] := by kernel_rfl

theorem native.checked7 :
    equal (CleanExpression.polynomial native.placement native.expression7)
        (combination native.relations native.witness7) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression7 native.witness7
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 7
    (by decide +kernel) native.idealCodeBinding7 native.idealRelationsBinding native.idealWitnessBinding7

theorem native.preserved7 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression7).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression7 native.placement native.relations native.witness7
    native.checked7 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression8 : Airbender.Expression Source.BaseField :=
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
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨64⟩))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField)))
                              (Airbender.Expression.var ⟨65⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.const (Int.cast (Int.ofNat 3) : Source.BaseField)))
                            (Airbender.Expression.var ⟨66⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField)))
                          (Airbender.Expression.var ⟨67⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.const (Int.cast (Int.ofNat 5) : Source.BaseField)))
                        (Airbender.Expression.var ⟨68⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.const (Int.cast (Int.ofNat 6) : Source.BaseField)))
                      (Airbender.Expression.var ⟨69⟩)))
                  (Airbender.Expression.var ⟨64⟩))
                (Airbender.Expression.var ⟨65⟩))
              (Airbender.Expression.var ⟨68⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                      (Airbender.Expression.var ⟨63⟩))
                    (Airbender.Expression.var ⟨66⟩))
                  (Airbender.Expression.var ⟨67⟩)))
              (Airbender.Expression.var ⟨74⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨69⟩))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 5) : Source.BaseField)))
                (Airbender.Expression.var ⟨74⟩)))))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField)))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨71⟩))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField)))
                    (Airbender.Expression.var ⟨72⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 3) : Source.BaseField)))
                  (Airbender.Expression.var ⟨73⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField)))
                (Airbender.Expression.var ⟨74⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                        (Airbender.Expression.var ⟨63⟩))
                      (Airbender.Expression.var ⟨66⟩))
                    (Airbender.Expression.var ⟨67⟩))
                  (Airbender.Expression.var ⟨69⟩)))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.negSucc 4) : Source.BaseField)))
                  (Airbender.Expression.var ⟨74⟩)))))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.const (Int.cast (Int.ofNat 64) : Source.BaseField)))
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨75⟩))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField)))
                    (Airbender.Expression.var ⟨76⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField)))
                  (Airbender.Expression.var ⟨77⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField)))
                (Airbender.Expression.var ⟨78⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 16) : Source.BaseField)))
              (Airbender.Expression.var ⟨79⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨69⟩))
            (Airbender.Expression.var ⟨74⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨5⟩))

noncomputable def native.witness8 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨40, by decide⟩)]

theorem native.idealCodeBinding8 :
    CleanIdealChecks.encode native.placement native.expression8 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 8 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding8 :
    NumericPolynomialChecks.encodeCombination native.witness8 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 8 [] := by kernel_rfl

theorem native.idealInputsBinding8 :
    CleanExpression.inputs native.expression8 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 8 [] := by kernel_rfl

theorem native.checked8 :
    equal (CleanExpression.polynomial native.placement native.expression8)
        (combination native.relations native.witness8) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression8 native.witness8
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 8
    (by decide +kernel) native.idealCodeBinding8 native.idealRelationsBinding native.idealWitnessBinding8

theorem native.preserved8 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression8).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression8 native.placement native.relations native.witness8
    native.checked8 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression9 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨67⟩))
        (Airbender.Expression.var ⟨70⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨80⟩))

noncomputable def native.witness9 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨41, by decide⟩)]

theorem native.idealCodeBinding9 :
    CleanIdealChecks.encode native.placement native.expression9 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 9 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding9 :
    NumericPolynomialChecks.encodeCombination native.witness9 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 9 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
