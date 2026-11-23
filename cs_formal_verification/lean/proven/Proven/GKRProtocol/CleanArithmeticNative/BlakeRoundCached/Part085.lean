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

local instance generatedBatch85Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch85Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression104 : Airbender.Expression Source.BaseField :=
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
                                                          (Airbender.Expression.var ⟨133⟩)))
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.const
                                                            (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                          (Airbender.Expression.var ⟨214⟩))
                                                        (Airbender.Expression.var ⟨33⟩)))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.var ⟨204⟩))
                                                      (Airbender.Expression.var ⟨117⟩)))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
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
                                                          (Airbender.Expression.var ⟨205⟩))))
                                                    (Airbender.Expression.var ⟨109⟩)))
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                    (Airbender.Expression.var ⟨205⟩))
                                                  (Airbender.Expression.var ⟨17⟩)))
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
                                                (Airbender.Expression.var ⟨111⟩)))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.var ⟨206⟩))
                                              (Airbender.Expression.var ⟨21⟩)))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.add
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
                                                    (Airbender.Expression.var ⟨207⟩)))
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                  (Airbender.Expression.var ⟨217⟩))))
                                            (Airbender.Expression.var ⟨119⟩)))
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.var ⟨217⟩))
                                          (Airbender.Expression.var ⟨5⟩)))
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                          (Airbender.Expression.var ⟨207⟩))
                                        (Airbender.Expression.var ⟨103⟩)))
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
                                      (Airbender.Expression.var ⟨129⟩)))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.var ⟨218⟩))
                                    (Airbender.Expression.var ⟨25⟩)))
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.var ⟨208⟩))
                                  (Airbender.Expression.var ⟨113⟩)))
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
                                (Airbender.Expression.var ⟨121⟩)))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.var ⟨219⟩))
                              (Airbender.Expression.var ⟨9⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.var ⟨209⟩))
                            (Airbender.Expression.var ⟨105⟩)))
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
                          (Airbender.Expression.var ⟨125⟩)))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                          (Airbender.Expression.var ⟨220⟩))
                        (Airbender.Expression.var ⟨17⟩)))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨210⟩))
                      (Airbender.Expression.var ⟨109⟩)))
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
                    (Airbender.Expression.var ⟨123⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨221⟩))
                  (Airbender.Expression.var ⟨13⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨211⟩))
                (Airbender.Expression.var ⟨107⟩)))
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
              (Airbender.Expression.var ⟨113⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨212⟩))
            (Airbender.Expression.var ⟨25⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨151⟩))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                (Airbender.Expression.var ⟨213⟩))))
          (Airbender.Expression.var ⟨103⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨213⟩))
        (Airbender.Expression.var ⟨5⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨254⟩))

noncomputable def native.witness104 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨194, by decide⟩)]

theorem native.idealCodeBinding104 :
    CleanIdealChecks.encode native.placement native.expression104 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 104 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding104 :
    NumericPolynomialChecks.encodeCombination native.witness104 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 104 [] := by kernel_rfl

theorem native.idealInputsBinding104 :
    CleanExpression.inputs native.expression104 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 104 [] := by kernel_rfl

theorem native.checked104 :
    equal (CleanExpression.polynomial native.placement native.expression104)
        (combination native.relations native.witness104) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression104 native.witness104
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 104 (by decide +kernel) native.idealCodeBinding104
    native.idealRelationsBinding native.idealWitnessBinding104

theorem native.preserved104 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression104).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression104 native.placement native.relations native.witness104
    native.checked104 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
