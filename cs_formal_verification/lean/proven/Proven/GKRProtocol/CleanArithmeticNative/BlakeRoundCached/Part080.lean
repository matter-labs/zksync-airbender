module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
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

local instance generatedBatch80Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch80Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression99 : Airbender.Expression Source.BaseField :=
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
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.const
                                                            (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                          (Airbender.Expression.add
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
                                                                (Airbender.Expression.var ⟨204⟩)))
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                              (Airbender.Expression.var ⟨214⟩))))
                                                        (Airbender.Expression.var ⟨128⟩)))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.var ⟨214⟩))
                                                      (Airbender.Expression.var ⟨22⟩)))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                      (Airbender.Expression.var ⟨204⟩))
                                                    (Airbender.Expression.var ⟨112⟩)))
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
                                                  (Airbender.Expression.var ⟨126⟩)))
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.const
                                                    (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                  (Airbender.Expression.var ⟨215⟩))
                                                (Airbender.Expression.var ⟨18⟩)))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.var ⟨205⟩))
                                              (Airbender.Expression.var ⟨110⟩)))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
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
                                                  (Airbender.Expression.var ⟨206⟩))))
                                            (Airbender.Expression.var ⟨118⟩)))
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.var ⟨206⟩))
                                          (Airbender.Expression.var ⟨34⟩)))
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
                                        (Airbender.Expression.var ⟨112⟩)))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.var ⟨207⟩))
                                      (Airbender.Expression.var ⟨22⟩)))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.add
                                        (Airbender.Expression.add
                                          (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                          (Airbender.Expression.var ⟨146⟩))
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.const
                                              (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                          (Airbender.Expression.var ⟨208⟩))))
                                    (Airbender.Expression.var ⟨116⟩)))
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.var ⟨208⟩))
                                  (Airbender.Expression.var ⟨30⟩)))
                              (Airbender.Expression.mul
                                (Airbender.Expression.mul
                                  (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                  (Airbender.Expression.add
                                    (Airbender.Expression.add
                                      (Airbender.Expression.add
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                        (Airbender.Expression.var ⟨147⟩))
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                          (Airbender.Expression.const
                                            (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                        (Airbender.Expression.var ⟨209⟩)))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                      (Airbender.Expression.var ⟨219⟩))))
                                (Airbender.Expression.var ⟨134⟩)))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.var ⟨219⟩))
                              (Airbender.Expression.var ⟨34⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.var ⟨209⟩))
                            (Airbender.Expression.var ⟨118⟩)))
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
                          (Airbender.Expression.var ⟨122⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨220⟩))
                        (Airbender.Expression.var ⟨10⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨210⟩))
                      (Airbender.Expression.var ⟨106⟩)))
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
                    (Airbender.Expression.var ⟨120⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨221⟩))
                  (Airbender.Expression.var ⟨6⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨211⟩))
                (Airbender.Expression.var ⟨104⟩)))
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
              (Airbender.Expression.var ⟨106⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨212⟩))
            (Airbender.Expression.var ⟨10⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨151⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                (Airbender.Expression.var ⟨213⟩))))
          (Airbender.Expression.var ⟨110⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨213⟩))
        (Airbender.Expression.var ⟨18⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨249⟩))

noncomputable def native.witness99 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨189, by decide⟩)]

theorem native.idealCodeBinding99 :
    CleanIdealChecks.encode native.placement native.expression99 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 99 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding99 :
    NumericPolynomialChecks.encodeCombination native.witness99 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 99 [] := by kernel_rfl

theorem native.idealInputsBinding99 :
    CleanExpression.inputs native.expression99 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 99 [] := by kernel_rfl

theorem native.checked99 :
    equal (CleanExpression.polynomial native.placement native.expression99)
        (combination native.relations native.witness99) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression99 native.witness99
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 99 (by decide +kernel) native.idealCodeBinding99
    native.idealRelationsBinding native.idealWitnessBinding99

theorem native.preserved99 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression99).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression99 native.placement native.relations native.witness99
    native.checked99 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
