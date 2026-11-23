module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part070
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

local instance generatedBatch71Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch71Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding82 :
    CleanIdealChecks.encode native.placement native.expression82 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 82 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding82 :
    NumericPolynomialChecks.encodeCombination native.witness82 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 82 [] := by kernel_rfl

theorem native.idealInputsBinding82 :
    CleanExpression.inputs native.expression82 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 82 [] := by kernel_rfl

theorem native.checked82 :
    equal (CleanExpression.polynomial native.placement native.expression82)
        (combination native.relations native.witness82) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression82 native.witness82
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 82
    (by decide +kernel) native.idealCodeBinding82 native.idealRelationsBinding native.idealWitnessBinding82

theorem native.preserved82 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression82).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression82 native.placement native.relations native.witness82
    native.checked82 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression83 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨210⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
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
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.add
                                                              (Airbender.Expression.add
                                                                (Airbender.Expression.add
                                                                  (Airbender.Expression.add
                                                                    (Airbender.Expression.add
                                                                      (Airbender.Expression.const
                                                                        (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                                      (Airbender.Expression.mul
                                                                        (Airbender.Expression.mul
                                                                          (Airbender.Expression.const
                                                                            (Int.cast (Int.ofNat 1) :
                                                                              Source.BaseField))
                                                                          (Airbender.Expression.var ⟨67⟩))
                                                                        (Airbender.Expression.var ⟨64⟩)))
                                                                    (Airbender.Expression.mul
                                                                      (Airbender.Expression.mul
                                                                        (Airbender.Expression.const
                                                                          (Int.cast (Int.ofNat 1) :
                                                                            Source.BaseField))
                                                                        (Airbender.Expression.var ⟨147⟩))
                                                                      (Airbender.Expression.var ⟨62⟩)))
                                                                  (Airbender.Expression.mul
                                                                    (Airbender.Expression.mul
                                                                      (Airbender.Expression.const
                                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                      (Airbender.Expression.var ⟨68⟩))
                                                                    (Airbender.Expression.var ⟨64⟩)))
                                                                (Airbender.Expression.mul
                                                                  (Airbender.Expression.mul
                                                                    (Airbender.Expression.const
                                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                    (Airbender.Expression.var ⟨148⟩))
                                                                  (Airbender.Expression.var ⟨62⟩)))
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.mul
                                                                  (Airbender.Expression.const
                                                                    (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                  (Airbender.Expression.var ⟨69⟩))
                                                                (Airbender.Expression.var ⟨64⟩)))
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                (Airbender.Expression.var ⟨149⟩))
                                                              (Airbender.Expression.var ⟨62⟩)))
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                              (Airbender.Expression.var ⟨70⟩))
                                                            (Airbender.Expression.var ⟨64⟩)))
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                            (Airbender.Expression.var ⟨150⟩))
                                                          (Airbender.Expression.var ⟨62⟩)))
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.const
                                                            (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                          (Airbender.Expression.var ⟨71⟩))
                                                        (Airbender.Expression.var ⟨64⟩)))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.var ⟨151⟩))
                                                      (Airbender.Expression.var ⟨62⟩)))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                      (Airbender.Expression.var ⟨72⟩))
                                                    (Airbender.Expression.var ⟨64⟩)))
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                    (Airbender.Expression.var ⟨152⟩))
                                                  (Airbender.Expression.var ⟨62⟩)))
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.const
                                                    (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                  (Airbender.Expression.var ⟨73⟩))
                                                (Airbender.Expression.var ⟨64⟩)))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.var ⟨153⟩))
                                              (Airbender.Expression.var ⟨62⟩)))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.var ⟨74⟩))
                                            (Airbender.Expression.var ⟨64⟩)))
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.var ⟨154⟩))
                                          (Airbender.Expression.var ⟨62⟩)))
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                          (Airbender.Expression.var ⟨75⟩))
                                        (Airbender.Expression.var ⟨64⟩)))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.var ⟨155⟩))
                                      (Airbender.Expression.var ⟨62⟩)))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.var ⟨76⟩))
                                    (Airbender.Expression.var ⟨64⟩)))
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.var ⟨156⟩))
                                  (Airbender.Expression.var ⟨62⟩)))
                              (Airbender.Expression.mul
                                (Airbender.Expression.mul
                                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                  (Airbender.Expression.var ⟨77⟩))
                                (Airbender.Expression.var ⟨64⟩)))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.var ⟨157⟩))
                              (Airbender.Expression.var ⟨62⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.var ⟨78⟩))
                            (Airbender.Expression.var ⟨64⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨158⟩))
                          (Airbender.Expression.var ⟨62⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨79⟩))
                        (Airbender.Expression.var ⟨64⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨159⟩))
                      (Airbender.Expression.var ⟨62⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨80⟩))
                    (Airbender.Expression.var ⟨64⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨160⟩))
                  (Airbender.Expression.var ⟨62⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨81⟩))
                (Airbender.Expression.var ⟨64⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨161⟩))
              (Airbender.Expression.var ⟨62⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨82⟩))
            (Airbender.Expression.var ⟨64⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨162⟩))
          (Airbender.Expression.var ⟨62⟩))))

noncomputable def native.witness83 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨58, by decide⟩)]

theorem native.idealCodeBinding83 :
    CleanIdealChecks.encode native.placement native.expression83 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 83 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding83 :
    NumericPolynomialChecks.encodeCombination native.witness83 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 83 [] := by kernel_rfl

theorem native.idealInputsBinding83 :
    CleanExpression.inputs native.expression83 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 83 [] := by kernel_rfl

theorem native.checked83 :
    equal (CleanExpression.polynomial native.placement native.expression83)
        (combination native.relations native.witness83) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression83 native.witness83
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 83
    (by decide +kernel) native.idealCodeBinding83 native.idealRelationsBinding native.idealWitnessBinding83

theorem native.preserved83 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression83).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression83 native.placement native.relations native.witness83
    native.checked83 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression84 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨213⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
      (Airbender.Expression.var ⟨211⟩))

noncomputable def native.witness84 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨59, by decide⟩)]

theorem native.idealCodeBinding84 :
    CleanIdealChecks.encode native.placement native.expression84 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 84 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding84 :
    NumericPolynomialChecks.encodeCombination native.witness84 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 84 [] := by kernel_rfl

theorem native.idealInputsBinding84 :
    CleanExpression.inputs native.expression84 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 84 [] := by kernel_rfl

theorem native.checked84 :
    equal (CleanExpression.polynomial native.placement native.expression84)
        (combination native.relations native.witness84) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression84 native.witness84
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 84
    (by decide +kernel) native.idealCodeBinding84 native.idealRelationsBinding native.idealWitnessBinding84

theorem native.preserved84 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression84).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression84 native.placement native.relations native.witness84
    native.checked84 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression85 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add (Airbender.Expression.var ⟨214⟩)
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField))
      (Airbender.Expression.var ⟨212⟩))

noncomputable def native.witness85 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨60, by decide⟩)]

theorem native.idealCodeBinding85 :
    CleanIdealChecks.encode native.placement native.expression85 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 85 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding85 :
    NumericPolynomialChecks.encodeCombination native.witness85 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 85 [] := by kernel_rfl

theorem native.idealInputsBinding85 :
    CleanExpression.inputs native.expression85 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 85 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
