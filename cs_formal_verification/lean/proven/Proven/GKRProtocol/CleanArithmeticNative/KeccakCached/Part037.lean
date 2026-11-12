module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part036
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

local instance generatedBatch37Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch37Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding81 :
    CleanExpression.inputs native.expression81 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 81 [] := by kernel_rfl

theorem native.checked81 :
    equal (CleanExpression.polynomial native.placement native.expression81)
        (combination native.relations native.witness81) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression81 native.witness81
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 81
    (by decide +kernel) native.idealCodeBinding81 native.idealRelationsBinding native.idealWitnessBinding81

theorem native.preserved81 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression81).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression81 native.placement native.relations native.witness81
    native.checked81 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression82 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                        (Airbender.Expression.var ⟨81⟩))
                      (Airbender.Expression.var ⟨84⟩))
                    (Airbender.Expression.var ⟨80⟩))
                  (Airbender.Expression.var ⟨82⟩))
                (Airbender.Expression.var ⟨83⟩)))))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨212⟩))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
            (Airbender.Expression.var ⟨213⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨52⟩))
                    (Airbender.Expression.var ⟨63⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨97⟩))
                  (Airbender.Expression.var ⟨64⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨60⟩))
                (Airbender.Expression.var ⟨65⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨60⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨97⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨44⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness82 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨114, by decide⟩)]

theorem native.idealCodeBinding82 :
    CleanIdealChecks.encode native.placement native.expression82 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 82 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding82 :
    NumericPolynomialChecks.encodeCombination native.witness82 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 82 [] := by kernel_rfl

theorem native.idealInputsBinding82 :
    CleanExpression.inputs native.expression82 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 82 [] := by kernel_rfl

theorem native.checked82 :
    equal (CleanExpression.polynomial native.placement native.expression82)
        (combination native.relations native.witness82) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression82 native.witness82
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 82
    (by decide +kernel) native.idealCodeBinding82 native.idealRelationsBinding native.idealWitnessBinding82

theorem native.preserved82 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression82).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression82 native.placement native.relations native.witness82
    native.checked82 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression83 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨81⟩))
                            (Airbender.Expression.var ⟨84⟩))
                          (Airbender.Expression.var ⟨80⟩))
                        (Airbender.Expression.var ⟨82⟩))
                      (Airbender.Expression.var ⟨83⟩)))))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨220⟩))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
                  (Airbender.Expression.var ⟨221⟩)))))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨81⟩))
                (Airbender.Expression.var ⟨84⟩)))
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.var ⟨217⟩))
              (Airbender.Expression.var ⟨208⟩))))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨80⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨216⟩))
            (Airbender.Expression.var ⟨207⟩))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨82⟩))
            (Airbender.Expression.var ⟨83⟩)))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨214⟩))
          (Airbender.Expression.var ⟨209⟩))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
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
                        (Airbender.Expression.var ⟨62⟩))
                      (Airbender.Expression.var ⟨63⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨38⟩))
                    (Airbender.Expression.var ⟨64⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨46⟩))
                  (Airbender.Expression.var ⟨65⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨54⟩))
                (Airbender.Expression.var ⟨66⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨54⟩))
              (Airbender.Expression.var ⟨67⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨30⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨22⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness83 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨115, by decide⟩)]

theorem native.idealCodeBinding83 :
    CleanIdealChecks.encode native.placement native.expression83 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 83 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding83 :
    NumericPolynomialChecks.encodeCombination native.witness83 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 83 [] := by kernel_rfl

theorem native.idealInputsBinding83 :
    CleanExpression.inputs native.expression83 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 83 [] := by kernel_rfl

theorem native.checked83 :
    equal (CleanExpression.polynomial native.placement native.expression83)
        (combination native.relations native.witness83) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression83 native.witness83
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 83
    (by decide +kernel) native.idealCodeBinding83 native.idealRelationsBinding native.idealWitnessBinding83

theorem native.preserved83 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression83).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression83 native.placement native.relations native.witness83
    native.checked83 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression84 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨23⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨25⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness84 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨116, by decide⟩)]

theorem native.idealCodeBinding84 :
    CleanIdealChecks.encode native.placement native.expression84 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 84 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding84 :
    NumericPolynomialChecks.encodeCombination native.witness84 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 84 [] := by kernel_rfl

theorem native.idealInputsBinding84 :
    CleanExpression.inputs native.expression84 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 84 [] := by kernel_rfl

theorem native.checked84 :
    equal (CleanExpression.polynomial native.placement native.expression84)
        (combination native.relations native.witness84) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression84 native.witness84
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 84
    (by decide +kernel) native.idealCodeBinding84 native.idealRelationsBinding native.idealWitnessBinding84

theorem native.preserved84 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression84).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression84 native.placement native.relations native.witness84
    native.checked84 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
