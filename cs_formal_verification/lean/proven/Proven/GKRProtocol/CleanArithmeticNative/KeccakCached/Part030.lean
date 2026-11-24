module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part029
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

local instance generatedBatch30Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch30Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding57 :
    CleanExpression.inputs native.expression57 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 57 [] := by kernel_rfl

theorem native.checked57 :
    equal (CleanExpression.polynomial native.placement native.expression57)
        (combination native.relations native.witness57) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression57 native.witness57
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 57
    (by decide +kernel) native.idealCodeBinding57 native.idealRelationsBinding native.idealWitnessBinding57

theorem native.preserved57 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression57).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression57 native.placement native.relations native.witness57
    native.checked57 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression58 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨64⟩))
      (Airbender.Expression.var ⟨67⟩))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨64⟩))
                (Airbender.Expression.var ⟨80⟩))
              (Airbender.Expression.var ⟨81⟩))
            (Airbender.Expression.var ⟨82⟩))
          (Airbender.Expression.var ⟨83⟩))
        (Airbender.Expression.var ⟨84⟩)))

noncomputable def native.witness58 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨51, by decide⟩)]

theorem native.idealCodeBinding58 :
    CleanIdealChecks.encode native.placement native.expression58 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 58 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding58 :
    NumericPolynomialChecks.encodeCombination native.witness58 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 58 [] := by kernel_rfl

theorem native.idealInputsBinding58 :
    CleanExpression.inputs native.expression58 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 58 [] := by kernel_rfl

theorem native.checked58 :
    equal (CleanExpression.polynomial native.placement native.expression58)
        (combination native.relations native.witness58) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression58 native.witness58
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 58
    (by decide +kernel) native.idealCodeBinding58 native.idealRelationsBinding native.idealWitnessBinding58

theorem native.preserved58 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression58).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression58 native.placement native.relations native.witness58
    native.checked58 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression59 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
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
                          (Airbender.Expression.add
                            (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                            (Airbender.Expression.var ⟨64⟩))
                          (Airbender.Expression.var ⟨82⟩))
                        (Airbender.Expression.var ⟨84⟩))
                      (Airbender.Expression.var ⟨83⟩))
                    (Airbender.Expression.var ⟨80⟩))
                  (Airbender.Expression.var ⟨81⟩)))))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨174⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
              (Airbender.Expression.var ⟨175⟩)))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                      (Airbender.Expression.var ⟨64⟩))
                    (Airbender.Expression.var ⟨82⟩))
                  (Airbender.Expression.var ⟨84⟩))
                (Airbender.Expression.var ⟨83⟩))
              (Airbender.Expression.var ⟨80⟩))
            (Airbender.Expression.var ⟨81⟩)))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨174⟩))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.negSucc 65535) : Source.BaseField)))
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
                          (Airbender.Expression.var ⟨80⟩))
                        (Airbender.Expression.const (Int.cast (Int.ofNat 9) : Source.BaseField))))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.var ⟨81⟩))
                      (Airbender.Expression.const (Int.cast (Int.ofNat 13) : Source.BaseField))))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨82⟩))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 15) : Source.BaseField))))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨83⟩))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 5) : Source.BaseField))))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨84⟩))
                (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField))))))))
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
                        (Airbender.Expression.var ⟨94⟩))
                      (Airbender.Expression.var ⟨63⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨47⟩))
                    (Airbender.Expression.var ⟨64⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨23⟩))
                  (Airbender.Expression.var ⟨65⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨39⟩))
                (Airbender.Expression.var ⟨66⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨39⟩))
              (Airbender.Expression.var ⟨67⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨31⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨31⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness59 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨91, by decide⟩)]

theorem native.idealCodeBinding59 :
    CleanIdealChecks.encode native.placement native.expression59 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 59 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding59 :
    NumericPolynomialChecks.encodeCombination native.witness59 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 59 [] := by kernel_rfl

theorem native.idealInputsBinding59 :
    CleanExpression.inputs native.expression59 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 59 [] := by kernel_rfl

theorem native.checked59 :
    equal (CleanExpression.polynomial native.placement native.expression59)
        (combination native.relations native.witness59) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression59 native.witness59
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 59
    (by decide +kernel) native.idealCodeBinding59 native.idealRelationsBinding native.idealWitnessBinding59

theorem native.preserved59 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression59).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression59 native.placement native.relations native.witness59
    native.checked59 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression60 : Airbender.Expression Source.BaseField :=
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
                        (Airbender.Expression.add
                          (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                          (Airbender.Expression.var ⟨64⟩))
                        (Airbender.Expression.var ⟨82⟩))
                      (Airbender.Expression.var ⟨84⟩))
                    (Airbender.Expression.var ⟨83⟩))
                  (Airbender.Expression.var ⟨80⟩))
                (Airbender.Expression.var ⟨81⟩)))))
        (Airbender.Expression.add
          (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
            (Airbender.Expression.var ⟨182⟩))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 256) : Source.BaseField)))
            (Airbender.Expression.var ⟨183⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨39⟩))
                  (Airbender.Expression.var ⟨63⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨94⟩))
                (Airbender.Expression.var ⟨65⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨55⟩))
              (Airbender.Expression.var ⟨66⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨39⟩))
            (Airbender.Expression.var ⟨68⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨94⟩))
          (Airbender.Expression.var ⟨69⟩))))

noncomputable def native.witness60 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨92, by decide⟩)]

theorem native.idealCodeBinding60 :
    CleanIdealChecks.encode native.placement native.expression60 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 60 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding60 :
    NumericPolynomialChecks.encodeCombination native.witness60 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 60 [] := by kernel_rfl

theorem native.idealInputsBinding60 :
    CleanExpression.inputs native.expression60 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 60 [] := by kernel_rfl

theorem native.checked60 :
    equal (CleanExpression.polynomial native.placement native.expression60)
        (combination native.relations native.witness60) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression60 native.witness60
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 60
    (by decide +kernel) native.idealCodeBinding60 native.idealRelationsBinding native.idealWitnessBinding60

theorem native.preserved60 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression60).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression60 native.placement native.relations native.witness60
    native.checked60 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
