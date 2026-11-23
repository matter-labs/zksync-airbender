module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part054
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch55Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch55Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding71 :
    CleanIdealChecks.encode native.placement native.expression71 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 71 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding71 :
    NumericPolynomialChecks.encodeCombination native.witness71 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 71 [] := by kernel_rfl

theorem native.idealInputsBinding71 :
    CleanExpression.inputs native.expression71 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 71 [] := by kernel_rfl

theorem native.checked71 :
    equal (CleanExpression.polynomial native.placement native.expression71)
        (combination native.relations native.witness71) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression71 native.witness71
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 71 (by decide +kernel) native.idealCodeBinding71
    native.idealRelationsBinding native.idealWitnessBinding71

theorem native.preserved71 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression71).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression71 native.placement native.relations native.witness71
    native.checked71 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression72 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨150⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨222⟩))

noncomputable def native.witness72 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨162, by decide⟩)]

theorem native.idealCodeBinding72 :
    CleanIdealChecks.encode native.placement native.expression72 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 72 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding72 :
    NumericPolynomialChecks.encodeCombination native.witness72 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 72 [] := by kernel_rfl

theorem native.idealInputsBinding72 :
    CleanExpression.inputs native.expression72 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 72 [] := by kernel_rfl

theorem native.checked72 :
    equal (CleanExpression.polynomial native.placement native.expression72)
        (combination native.relations native.witness72) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression72 native.witness72
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 72 (by decide +kernel) native.idealCodeBinding72
    native.idealRelationsBinding native.idealWitnessBinding72

theorem native.preserved72 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression72).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression72 native.placement native.relations native.witness72
    native.checked72 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression73 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨151⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨223⟩))

noncomputable def native.witness73 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨163, by decide⟩)]

theorem native.idealCodeBinding73 :
    CleanIdealChecks.encode native.placement native.expression73 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 73 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding73 :
    NumericPolynomialChecks.encodeCombination native.witness73 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 73 [] := by kernel_rfl

theorem native.idealInputsBinding73 :
    CleanExpression.inputs native.expression73 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 73 [] := by kernel_rfl

theorem native.checked73 :
    equal (CleanExpression.polynomial native.placement native.expression73)
        (combination native.relations native.witness73) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression73 native.witness73
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 73 (by decide +kernel) native.idealCodeBinding73
    native.idealRelationsBinding native.idealWitnessBinding73

theorem native.preserved73 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression73).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression73 native.placement native.relations native.witness73
    native.checked73 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression74 : Airbender.Expression Source.BaseField :=
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
                                                              (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                            (Airbender.Expression.add
                                                              (Airbender.Expression.add
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                                (Airbender.Expression.var ⟨142⟩))
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.mul
                                                                  (Airbender.Expression.const
                                                                    (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                  (Airbender.Expression.const
                                                                    (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                                (Airbender.Expression.var ⟨204⟩))))
                                                          (Airbender.Expression.var ⟨103⟩)))
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.const
                                                            (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                          (Airbender.Expression.var ⟨204⟩))
                                                        (Airbender.Expression.var ⟨5⟩)))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.add
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.add
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                              (Airbender.Expression.var ⟨143⟩))
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                              (Airbender.Expression.var ⟨205⟩)))
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                            (Airbender.Expression.var ⟨215⟩))))
                                                      (Airbender.Expression.var ⟨131⟩)))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                      (Airbender.Expression.var ⟨215⟩))
                                                    (Airbender.Expression.var ⟨29⟩)))
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                    (Airbender.Expression.var ⟨205⟩))
                                                  (Airbender.Expression.var ⟨115⟩)))
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.const
                                                    (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                  (Airbender.Expression.add
                                                    (Airbender.Expression.add
                                                      (Airbender.Expression.add
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                        (Airbender.Expression.var ⟨144⟩))
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.const
                                                            (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                          (Airbender.Expression.const
                                                            (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                        (Airbender.Expression.var ⟨206⟩)))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                      (Airbender.Expression.var ⟨216⟩))))
                                                (Airbender.Expression.var ⟨125⟩)))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.var ⟨216⟩))
                                              (Airbender.Expression.var ⟨17⟩)))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.var ⟨206⟩))
                                            (Airbender.Expression.var ⟨109⟩)))
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.add
                                              (Airbender.Expression.add
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                (Airbender.Expression.var ⟨145⟩))
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.const
                                                    (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                  (Airbender.Expression.const
                                                    (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                (Airbender.Expression.var ⟨207⟩))))
                                          (Airbender.Expression.var ⟨117⟩)))
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                          (Airbender.Expression.var ⟨207⟩))
                                        (Airbender.Expression.var ⟨33⟩)))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.add
                                          (Airbender.Expression.add
                                            (Airbender.Expression.add
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 0) : Source.BaseField))
                                              (Airbender.Expression.var ⟨146⟩))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                              (Airbender.Expression.var ⟨208⟩)))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.const
                                                (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                            (Airbender.Expression.var ⟨218⟩))))
                                      (Airbender.Expression.var ⟨121⟩)))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.var ⟨218⟩))
                                    (Airbender.Expression.var ⟨9⟩)))
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.var ⟨208⟩))
                                  (Airbender.Expression.var ⟨105⟩)))
                              (Airbender.Expression.mul
                                (Airbender.Expression.mul
                                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                  (Airbender.Expression.add
                                    (Airbender.Expression.add
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                      (Airbender.Expression.var ⟨147⟩))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                      (Airbender.Expression.var ⟨209⟩))))
                                (Airbender.Expression.var ⟨107⟩)))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.var ⟨209⟩))
                              (Airbender.Expression.var ⟨13⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.add
                                (Airbender.Expression.add
                                  (Airbender.Expression.add
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                    (Airbender.Expression.var ⟨148⟩))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                    (Airbender.Expression.var ⟨210⟩)))
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                  (Airbender.Expression.var ⟨220⟩))))
                            (Airbender.Expression.var ⟨127⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨220⟩))
                          (Airbender.Expression.var ⟨21⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨210⟩))
                        (Airbender.Expression.var ⟨111⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨149⟩))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                              (Airbender.Expression.var ⟨211⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                            (Airbender.Expression.var ⟨221⟩))))
                      (Airbender.Expression.var ⟨129⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨221⟩))
                    (Airbender.Expression.var ⟨25⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨211⟩))
                  (Airbender.Expression.var ⟨113⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                      (Airbender.Expression.var ⟨150⟩))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                      (Airbender.Expression.var ⟨212⟩))))
                (Airbender.Expression.var ⟨115⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨212⟩))
              (Airbender.Expression.var ⟨29⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨151⟩))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                    (Airbender.Expression.var ⟨213⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                  (Airbender.Expression.var ⟨223⟩))))
            (Airbender.Expression.var ⟨123⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨223⟩))
          (Airbender.Expression.var ⟨13⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨213⟩))
        (Airbender.Expression.var ⟨107⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨224⟩))

noncomputable def native.witness74 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨164, by decide⟩)]

theorem native.idealCodeBinding74 :
    CleanIdealChecks.encode native.placement native.expression74 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 74 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding74 :
    NumericPolynomialChecks.encodeCombination native.witness74 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 74 [] := by kernel_rfl

theorem native.idealInputsBinding74 :
    CleanExpression.inputs native.expression74 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 74 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
