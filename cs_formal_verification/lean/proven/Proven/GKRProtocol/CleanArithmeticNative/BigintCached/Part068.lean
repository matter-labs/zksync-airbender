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

local instance generatedBatch68Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch68Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression72 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨72⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨72⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨72⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨14⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨136⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨152⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨72⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨16⟩))

noncomputable def native.witness72 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨118, by decide⟩)]

theorem native.idealCodeBinding72 :
    CleanIdealChecks.encode native.placement native.expression72 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 72 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding72 :
    NumericPolynomialChecks.encodeCombination native.witness72 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 72 [] := by kernel_rfl

theorem native.idealInputsBinding72 :
    CleanExpression.inputs native.expression72 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 72 [] := by kernel_rfl

theorem native.checked72 :
    equal (CleanExpression.polynomial native.placement native.expression72)
        (combination native.relations native.witness72) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression72 native.witness72
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 72
    (by decide +kernel) native.idealCodeBinding72 native.idealRelationsBinding native.idealWitnessBinding72

theorem native.preserved72 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression72).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression72 native.placement native.relations native.witness72
    native.checked72 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression73 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨73⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨73⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨73⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨17⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨137⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨153⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨73⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨19⟩))

noncomputable def native.witness73 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨119, by decide⟩)]

theorem native.idealCodeBinding73 :
    CleanIdealChecks.encode native.placement native.expression73 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 73 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding73 :
    NumericPolynomialChecks.encodeCombination native.witness73 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 73 [] := by kernel_rfl

theorem native.idealInputsBinding73 :
    CleanExpression.inputs native.expression73 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 73 [] := by kernel_rfl

theorem native.checked73 :
    equal (CleanExpression.polynomial native.placement native.expression73)
        (combination native.relations native.witness73) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression73 native.witness73
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 73
    (by decide +kernel) native.idealCodeBinding73 native.idealRelationsBinding native.idealWitnessBinding73

theorem native.preserved73 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression73).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression73 native.placement native.relations native.witness73
    native.checked73 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression74 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨74⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨74⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨74⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨18⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨138⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨154⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨74⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨20⟩))

noncomputable def native.witness74 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨120, by decide⟩)]

theorem native.idealCodeBinding74 :
    CleanIdealChecks.encode native.placement native.expression74 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 74 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding74 :
    NumericPolynomialChecks.encodeCombination native.witness74 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 74 [] := by kernel_rfl

theorem native.idealInputsBinding74 :
    CleanExpression.inputs native.expression74 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 74 [] := by kernel_rfl

theorem native.checked74 :
    equal (CleanExpression.polynomial native.placement native.expression74)
        (combination native.relations native.witness74) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression74 native.witness74
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 74
    (by decide +kernel) native.idealCodeBinding74 native.idealRelationsBinding native.idealWitnessBinding74

theorem native.preserved74 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression74).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression74 native.placement native.relations native.witness74
    native.checked74 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression75 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨75⟩))
                    (Airbender.Expression.var ⟨59⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨75⟩))
                  (Airbender.Expression.var ⟨60⟩)))
              (Airbender.Expression.mul
                (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                  (Airbender.Expression.var ⟨75⟩))
                (Airbender.Expression.var ⟨61⟩)))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.var ⟨21⟩))
              (Airbender.Expression.var ⟨64⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨139⟩))
            (Airbender.Expression.var ⟨62⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨155⟩))
          (Airbender.Expression.var ⟨63⟩)))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨75⟩))
        (Airbender.Expression.var ⟨66⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨23⟩))

noncomputable def native.witness75 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨121, by decide⟩)]

theorem native.idealCodeBinding75 :
    CleanIdealChecks.encode native.placement native.expression75 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 75 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
