module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
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

local instance generatedBatch14Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch14Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked2 :
    equal (CleanExpression.polynomial native.placement native.expression2)
        (combination native.relations native.witness2) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression2 native.witness2
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 2
    (by decide +kernel) native.idealCodeBinding2 native.idealRelationsBinding native.idealWitnessBinding2

theorem native.preserved2 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression2).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression2 native.placement native.relations native.witness2
    native.checked2 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression3 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
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
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField)))
                (Airbender.Expression.var ⟨67⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 5) : Source.BaseField)))
              (Airbender.Expression.var ⟨68⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 6) : Source.BaseField)))
            (Airbender.Expression.var ⟨69⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField)))
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨71⟩))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField)))
                  (Airbender.Expression.var ⟨72⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 3) : Source.BaseField)))
                (Airbender.Expression.var ⟨73⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField)))
              (Airbender.Expression.var ⟨74⟩)))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.const (Int.cast (Int.ofNat 64) : Source.BaseField)))
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨75⟩))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.ofNat 2) : Source.BaseField)))
                  (Airbender.Expression.var ⟨76⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.const (Int.cast (Int.ofNat 4) : Source.BaseField)))
                (Airbender.Expression.var ⟨77⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.ofNat 8) : Source.BaseField)))
              (Airbender.Expression.var ⟨78⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.const (Int.cast (Int.ofNat 16) : Source.BaseField)))
            (Airbender.Expression.var ⟨79⟩)))))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨3⟩))

noncomputable def native.witness3 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨35, by decide⟩)]

theorem native.idealCodeBinding3 :
    CleanIdealChecks.encode native.placement native.expression3 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 3 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding3 :
    NumericPolynomialChecks.encodeCombination native.witness3 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 3 [] := by kernel_rfl

theorem native.idealInputsBinding3 :
    CleanExpression.inputs native.expression3 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 3 [] := by kernel_rfl

theorem native.checked3 :
    equal (CleanExpression.polynomial native.placement native.expression3)
        (combination native.relations native.witness3) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression3 native.witness3
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 3
    (by decide +kernel) native.idealCodeBinding3 native.idealRelationsBinding native.idealWitnessBinding3

theorem native.preserved3 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression3).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression3 native.placement native.relations native.witness3
    native.checked3 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression4 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨0⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨63⟩))
                  (Airbender.Expression.var ⟨64⟩))
                (Airbender.Expression.var ⟨65⟩))
              (Airbender.Expression.var ⟨66⟩))
            (Airbender.Expression.var ⟨67⟩))
          (Airbender.Expression.var ⟨68⟩))
        (Airbender.Expression.var ⟨69⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness4 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨36, by decide⟩)]

theorem native.idealCodeBinding4 :
    CleanIdealChecks.encode native.placement native.expression4 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 4 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding4 :
    NumericPolynomialChecks.encodeCombination native.witness4 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 4 [] := by kernel_rfl

theorem native.idealInputsBinding4 :
    CleanExpression.inputs native.expression4 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 4 [] := by kernel_rfl

theorem native.checked4 :
    equal (CleanExpression.polynomial native.placement native.expression4)
        (combination native.relations native.witness4) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression4 native.witness4
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 4
    (by decide +kernel) native.idealCodeBinding4 native.idealRelationsBinding native.idealWitnessBinding4

theorem native.preserved4 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression4).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression4 native.placement native.relations native.witness4
    native.checked4 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression5 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨0⟩))
    (Airbender.Expression.add
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
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness5 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨37, by decide⟩)]

theorem native.idealCodeBinding5 :
    CleanIdealChecks.encode native.placement native.expression5 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 5 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding5 :
    NumericPolynomialChecks.encodeCombination native.witness5 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 5 [] := by kernel_rfl

theorem native.idealInputsBinding5 :
    CleanExpression.inputs native.expression5 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 5 [] := by kernel_rfl

theorem native.checked5 :
    equal (CleanExpression.polynomial native.placement native.expression5)
        (combination native.relations native.witness5) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression5 native.witness5
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 5
    (by decide +kernel) native.idealCodeBinding5 native.idealRelationsBinding native.idealWitnessBinding5

theorem native.preserved5 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression5).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression5 native.placement native.relations native.witness5
    native.checked5 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression6 : Airbender.Expression Source.BaseField :=
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
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.var ⟨63⟩))
                (Airbender.Expression.var ⟨64⟩))
              (Airbender.Expression.var ⟨65⟩))
            (Airbender.Expression.var ⟨66⟩))
          (Airbender.Expression.var ⟨67⟩))
        (Airbender.Expression.var ⟨68⟩))
      (Airbender.Expression.var ⟨69⟩))
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
